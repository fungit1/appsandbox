/*
 * appsandbox-clipboard.exe — Guest-side clipboard writer for AppSandbox.
 *
 * Runs as the interactive user (spawned by the agent service on Winsta0\Default
 * with the console user's token). Listens on AF_HYPERV socket (GUID :0005) for
 * the host IDD display to connect. Handles the host→guest clipboard direction:
 *   - On FORMAT_LIST from host: stores format metadata. Small formats
 *     (text, HTML, bitmap, ...) are fetched immediately; files (CF_HDROP)
 *     are downloaded in the background and added when complete.
 *   - On WM_RENDERFORMAT (the user pasted): requests the files via
 *     FORMAT_DATA_REQ happens in the background after the list arrives.
 *     finished CF_HDROP to the clipboard.
 *
 * Guest→host clipboard is handled separately by appsandbox-clipboard-reader.exe
 * (USER, GUID :0006).
 *
 * Logs to C:\Windows\AppSandbox\clipboard.log (beside agent.log).
 */

#include <winsock2.h>
#include <windows.h>
#include <wtsapi32.h>
#include <userenv.h>
#include <stdio.h>
#include <stdarg.h>
#include <shellapi.h>
#include <shlobj.h>
#include <objbase.h>
#include <shlwapi.h>
#pragma comment(lib, "ole32.lib")
#pragma comment(lib, "oleaut32.lib")
#include "../transport/asb_transport.h"   /* AF_HYPERV on PC, ivshmem on Mac */

#pragma comment(lib, "ws2_32.lib")
#pragma comment(lib, "user32.lib")
#pragma comment(lib, "shell32.lib")
#pragma comment(lib, "wtsapi32.lib")
#pragma comment(lib, "userenv.lib")

/* ---- Hyper-V socket definitions ---- */

#define AF_HYPERV 34

typedef struct _SOCKADDR_HV {
    ADDRESS_FAMILY Family;
    USHORT Reserved;
    GUID VmId;
    GUID ServiceId;
} SOCKADDR_HV;

static const GUID HV_GUID_WILDCARD =
    { 0, 0, 0, { 0, 0, 0, 0, 0, 0, 0, 0 } };

/* Clipboard channel: {A5B0CAFE-0005-4000-8000-000000000001} */
static const GUID CLIPBOARD_SERVICE_GUID =
    { 0xa5b0cafe, 0x0005, 0x4000, { 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 } };

/* ---- Clipboard protocol ---- */

#define CLIP_MAGIC          0x504C4341  /* "ACLP" little-endian */
#define CLIP_READY_MAGIC    0x59444C43  /* "CLDY" little-endian */

/* Protocol: delayed rendering (like MS-RDPECLIP) */
#define CLIP_MSG_FORMAT_LIST      1
#define CLIP_MSG_FORMAT_DATA_REQ  2
#define CLIP_MSG_FORMAT_DATA_RESP 3
#define CLIP_MSG_FILE_DATA        4
#define CLIP_MSG_SYNC_ENABLE      12
#define CLIP_MSG_FILE_LIST        5
#define CLIP_MSG_FILE_DATA_REQ    6

#define CLIP_MAX_FORMATS    64
#define CLIP_MAX_PAYLOAD    (64 * 1024 * 1024)  /* 64 MB */

#define WM_CLIP_APPLY_FMTS (WM_USER + 200)

#pragma pack(push, 1)
typedef struct {
    UINT32 magic;
    UINT32 msg_type;
    UINT32 format;
    UINT32 data_size;
} ClipHeader;
#pragma pack(pop)

/* Format entry: maps local↔remote IDs and holds fetched data */
typedef struct {
    UINT   local_id;
    UINT   remote_id;
    BYTE  *data;
    UINT32 data_size;
    BOOL   is_hdrop;
} ClipFmtEntry;

/* File transfer for CF_HDROP */
#define CLIP_FILE_CHUNK     (1024 * 1024)  /* 1 MB — HV socket is basically memcpy */
static wchar_t g_clip_temp_dir[MAX_PATH];

/* Registered clipboard formats for on-demand file streaming. */
static UINT g_cf_file_desc = 0;   /* CFSTR_FILEDESCRIPTORW */
static UINT g_cf_file_contents = 0; /* CFSTR_FILECONTENTS */

#pragma pack(push, 1)
typedef struct {
    UINT32 path_len;     /* relative path length in bytes (UTF-16LE, no null) */
    UINT64 file_size;    /* file data bytes that follow (0 for directories) */
    UINT8  is_directory; /* 1 = directory entry, 0 = regular file */
} ClipFileInfo;
#pragma pack(pop)

/* Format data: filled by recv thread, applied by wndproc */
static ClipFmtEntry g_clip_fmts[CLIP_MAX_FORMATS];
static int          g_clip_fmt_count = 0;
static int          g_clip_fetch_idx = 0;

/* File metadata for FileContents (lazy streaming). */
#define META_MAX 4096
typedef struct {
    wchar_t name[MAX_PATH];
    UINT64  size;
    DWORD   attrs;
    int     is_dir;
} FileMeta;
static FileMeta g_file_meta[META_MAX];
static int      g_file_meta_count = 0;

/* On-demand file transfer for FileContents.  Only one file is streamed at a
 * time: the shell copies items sequentially and COM serialises calls into our
 * STA.  The recv thread fills the temp file while the IStream reader drains it,
 * so Explorer's progress dialog advances during the transfer instead of
 * waiting for the whole file. */
static volatile LONG g_file_req_pending = 0;  /* recv thread must fetch */
static volatile LONG g_file_req_idx = 0;
static CRITICAL_SECTION g_xfer_cs;
static HANDLE g_xfer_event = NULL;   /* auto-reset: new bytes or transfer done */
static HANDLE g_xfer_start = NULL;   /* auto-reset: temp file created */
static int      g_xfer_active = 0;
static int      g_xfer_done = 0;
static int      g_xfer_error = 0;
static UINT64   g_xfer_written = 0;
static UINT64   g_xfer_total = 0;
static wchar_t  g_xfer_path[MAX_PATH];

/* Echo suppression */
static volatile LONG g_suppress = 0;

/* Focus-gated sync: host sends SYNC_ENABLE(0/1) on :0005.
 * When disabled, we ignore FORMAT_LIST and don't apply to clipboard.
 * The named event is shared with appsandbox-clipboard-reader.exe so
 * it can gate guest->host FORMAT_LIST sending. */
static volatile LONG g_sync_enabled = 0;
static HANDLE g_sync_event = NULL;
#define CLIP_SYNC_EVENT_NAME L"Global\\AppSandboxClipSync"

/* Socket shared between threads */
static AsbConn * volatile g_client_sock = NULL;
static CRITICAL_SECTION g_send_cs;

/* Message window (created on msg_window_thread) */
static HWND g_msg_hwnd = NULL;

/* State for the background file fetch (Option 2, made safe): the guest
 * advertises files only once they have actually been downloaded into the temp
 * folder, so a paste never blocks on a multi-gigabyte transfer and no
 * clipboard probe (Explorer menus, clipboard history, ...) can trigger one.
 * g_list_gen is bumped for every FORMAT_LIST; g_fetch_gen records which list
 * the in-flight fetch belongs to so a stale response is ignored. */
static CRITICAL_SECTION g_state_cs;
static volatile LONG g_list_has_hdrop = 0;
static volatile LONG g_apply_pending = 0;
static ULONGLONG     g_meta_deadline = 0;
static volatile LONG g_list_gen = 0;
static volatile LONG g_fetch_gen = 0;
static volatile LONG g_file_fetch_active = 0;
static volatile LONG g_applied_gen = 0;
static volatile LONG g_applied_seq = 0;
static volatile LONG g_applied_has_nonfile = 0;
#define WM_CLIP_ADD_FILES (WM_USER + 202)

/* ---- Logging ---- */

static void clip_log(const char *fmt, ...)
{
    FILE *f;
    va_list ap;
    SYSTEMTIME st;

    if (fopen_s(&f, "C:\\Windows\\AppSandbox\\clipboard.log", "a") != 0 || !f)
        return;
    GetLocalTime(&st);
    fprintf(f, "[%04d-%02d-%02d %02d:%02d:%02d] ",
        st.wYear, st.wMonth, st.wDay,
        st.wHour, st.wMinute, st.wSecond);
    va_start(ap, fmt);
    vfprintf(f, fmt, ap);
    va_end(ap);
    fprintf(f, "\n");
    fclose(f);
}

/* ---- Reliable send/recv ---- */

static BOOL send_all(AsbConn *s, const void *buf, int len)
{
    return asb_send(s, buf, len) == len;
}

static BOOL recv_exact(AsbConn *s, void *buf, int len)
{
    int got = 0;
    while (got < len) {
        int n = asb_recv(s, (char *)buf + got, len - got);
        if (n <= 0) return FALSE;
        got += n;
    }
    return TRUE;
}

/* ---- Send helpers ---- */

static BOOL send_all_locked(const void *buf, int len)
{
    AsbConn *s = g_client_sock;
    if (!s) return FALSE;
    return asb_send(s, buf, len) == len;
}

/* ---- Send clipboard to host ---- */

static void clip_init_temp_dir(void)
{
    DWORD session_id = WTSGetActiveConsoleSessionId();
    HANDLE user_token = NULL;
    wchar_t tmp[MAX_PATH];

    /* Get the logged-in user's token so we can resolve their %TEMP% */
    if (session_id != 0xFFFFFFFF &&
        WTSQueryUserToken(session_id, &user_token)) {
        if (ExpandEnvironmentStringsForUserW(user_token, L"%TEMP%",
                                              tmp, MAX_PATH)) {
            swprintf_s(g_clip_temp_dir, MAX_PATH, L"%s\\AppSandboxClip", tmp);
            CloseHandle(user_token);
            CreateDirectoryW(g_clip_temp_dir, NULL);
            clip_log("Temp dir: %ls", g_clip_temp_dir);
            return;
        }
        CloseHandle(user_token);
    }

    /* Fallback: SYSTEM temp (should not normally happen) */
    GetTempPathW(MAX_PATH, tmp);
    swprintf_s(g_clip_temp_dir, MAX_PATH, L"%sAppSandboxClip", tmp);
    CreateDirectoryW(g_clip_temp_dir, NULL);
    clip_log("Temp dir (fallback): %ls", g_clip_temp_dir);
}

/* ---- File transfer helpers ---- */

static void clip_remove_dir_recursive(const wchar_t *dir)
{
    WIN32_FIND_DATAW fd;
    wchar_t pattern[MAX_PATH];
    HANDLE h;
    swprintf_s(pattern, MAX_PATH, L"%s\\*", dir);
    h = FindFirstFileW(pattern, &fd);
    if (h == INVALID_HANDLE_VALUE) return;
    do {
        wchar_t path[MAX_PATH];
        if (wcscmp(fd.cFileName, L".") == 0 || wcscmp(fd.cFileName, L"..") == 0) continue;
        swprintf_s(path, MAX_PATH, L"%s\\%s", dir, fd.cFileName);
        if (fd.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY)
            clip_remove_dir_recursive(path);
        else
            DeleteFileW(path);
    } while (FindNextFileW(h, &fd));
    FindClose(h);
    RemoveDirectoryW(dir);
}

static void clip_ensure_parent_dir(const wchar_t *file_path)
{
    wchar_t dir[MAX_PATH];
    wchar_t *p;
    wcscpy_s(dir, MAX_PATH, file_path);
    p = wcsrchr(dir, L'\\');
    if (!p) return;
    *p = L'\0';
    for (p = dir; *p; p++) {
        if (*p == L'\\' && p > dir && *(p - 1) != L':') {
            *p = L'\0';
            CreateDirectoryW(dir, NULL);
            *p = L'\\';
        }
    }
    CreateDirectoryW(dir, NULL);
}

static BOOL clip_path_is_safe(const wchar_t *rel_path)
{
    if (wcsstr(rel_path, L"..")) return FALSE;
    if (rel_path[0] == L'\\' || rel_path[0] == L'/') return FALSE;
    if (wcslen(rel_path) > MAX_PATH - 50) return FALSE;
    return TRUE;
}

static HGLOBAL clip_build_hdrop_from_temp(void)
{
    WIN32_FIND_DATAW fd;
    wchar_t pattern[MAX_PATH];
    HANDLE h;
    wchar_t paths[CLIP_MAX_FORMATS][MAX_PATH];
    int count = 0;
    SIZE_T total_size;
    HGLOBAL hMem;
    DROPFILES *df;
    wchar_t *ptr;
    int i;

    swprintf_s(pattern, MAX_PATH, L"%s\\*", g_clip_temp_dir);
    h = FindFirstFileW(pattern, &fd);
    if (h == INVALID_HANDLE_VALUE) return NULL;
    do {
        if (wcscmp(fd.cFileName, L".") == 0 || wcscmp(fd.cFileName, L"..") == 0) continue;
        swprintf_s(paths[count], MAX_PATH, L"%s\\%s", g_clip_temp_dir, fd.cFileName);
        count++;
        if (count >= CLIP_MAX_FORMATS) break;
    } while (FindNextFileW(h, &fd));
    FindClose(h);
    if (count == 0) return NULL;

    total_size = sizeof(DROPFILES);
    for (i = 0; i < count; i++)
        total_size += (wcslen(paths[i]) + 1) * sizeof(wchar_t);
    total_size += sizeof(wchar_t);

    hMem = GlobalAlloc(GMEM_MOVEABLE | GMEM_ZEROINIT, total_size);
    if (!hMem) return NULL;
    df = (DROPFILES *)GlobalLock(hMem);
    if (!df) { GlobalFree(hMem); return NULL; }
    df->pFiles = sizeof(DROPFILES);
    df->fWide = TRUE;
    ptr = (wchar_t *)((BYTE *)df + sizeof(DROPFILES));
    for (i = 0; i < count; i++) {
        /* destsz must be this entry's reserved slice (wcslen+1), NOT MAX_PATH:
           the buffer is sized tightly per path (see total_size above), so passing
           MAX_PATH makes wcscpy_s's secure-CRT tail-fill memset run past the
           allocation -> heap overflow (caught by full page heap at memset). */
        wcscpy_s(ptr, wcslen(paths[i]) + 1, paths[i]);
        ptr += wcslen(paths[i]) + 1;
    }
    *ptr = L'\0';
    GlobalUnlock(hMem);
    return hMem;
}

/* Free all pending format data */
static void clip_free_pending(void)
{
    int i;
    for (i = 0; i < g_clip_fmt_count; i++) {
        if (g_clip_fmts[i].data) {
            HeapFree(GetProcessHeap(), 0, g_clip_fmts[i].data);
            g_clip_fmts[i].data = NULL;
        }
    }
}

/* Send FORMAT_DATA_REQ for the next eagerly fetched format, or post
   WM_CLIP_APPLY_FMTS if all of them are done. CF_HDROP entries are skipped:
   files are rendered lazily, when the user pastes. Called from recv thread. */
static void clip_request_next_format(void)
{
    ClipHeader hdr;

    /* Skip file entries - they are fetched in the background after apply. */
    while (g_clip_fetch_idx < g_clip_fmt_count &&
           g_clip_fmts[g_clip_fetch_idx].is_hdrop)
        g_clip_fetch_idx++;

    if (g_clip_fetch_idx >= g_clip_fmt_count) {
        /* Everything that needs to be here now has arrived - tell msg window
           to apply. If the list has files, wait until the metadata message
           (sent right after the format list) has been read, so the apply can
           advertise the files lazily instead of downloading them. */
        clip_log("Metadata formats fetched, applying.");
        if (g_list_has_hdrop) {
            InterlockedExchange(&g_apply_pending, 1);
        } else if (g_msg_hwnd) {
            PostMessageW(g_msg_hwnd, WM_CLIP_APPLY_FMTS, 0, 0);
        }
        return;
    }

    hdr.magic = CLIP_MAGIC;
    hdr.msg_type = CLIP_MSG_FORMAT_DATA_REQ;
    hdr.format = g_clip_fmts[g_clip_fetch_idx].remote_id;
    hdr.data_size = 0;

    EnterCriticalSection(&g_send_cs);
    send_all_locked(&hdr, sizeof(hdr));
    LeaveCriticalSection(&g_send_cs);

    clip_log("Requesting format %u (remote=%u) [%d/%d].",
             g_clip_fmts[g_clip_fetch_idx].local_id,
             g_clip_fmts[g_clip_fetch_idx].remote_id,
             g_clip_fetch_idx + 1, g_clip_fmt_count);
}

/* Apply the format list to the clipboard.
   Small formats are applied with their fetched data; CF_HDROP is put on the
   clipboard with delayed rendering (SetClipboardData(fmt, NULL)) so that the
   files are only downloaded when the user actually pastes.
   Called on the message window thread via WM_CLIP_APPLY_FMTS. */
/* ---- COM IDataObject / IStream for on-demand FileContents ---- */

#define SMALL_MAX 64

typedef struct {
    UINT    fmt;
    HGLOBAL h;
    SIZE_T  size;
} SmallFmt;

typedef struct {
    IDataObjectVtbl *lpVtbl;
    LONG ref;
    SmallFmt smalls[SMALL_MAX];
    int small_count;
    FileMeta *meta;          /* snapshot of the pushed file list */
    int meta_count;
} AsbDO;

typedef struct {
    IStreamVtbl *lpVtbl;
    LONG ref;
    int index;
    UINT64 declared_size;
    UINT64 pos;
    HANDLE hFile;
    wchar_t temp_path[MAX_PATH];
    int started;
} FileContentsStream;

static IStreamVtbl FCS_Vtbl;
static IEnumFORMATETCVtbl EN_Vtbl;

/* ---------- IStream: reads straight from the growing temp file ---------- */

static HRESULT STDMETHODCALLTYPE FCS_QueryInterface(IStream *this, REFIID riid, void **ppv)
{
    if (!ppv) return E_INVALIDARG;
    if (IsEqualIID(riid, &IID_IUnknown) || IsEqualIID(riid, &IID_IStream)) {
        *ppv = this;
        this->lpVtbl->AddRef(this);
        return S_OK;
    }
    *ppv = NULL;
    return E_NOINTERFACE;
}

static ULONG STDMETHODCALLTYPE FCS_AddRef(IStream *this)
{
    return (ULONG)InterlockedIncrement(&((FileContentsStream *)this)->ref);
}

static ULONG STDMETHODCALLTYPE FCS_Release(IStream *this)
{
    FileContentsStream *s = (FileContentsStream *)this;
    ULONG r = (ULONG)InterlockedDecrement(&s->ref);
    if (r == 0) {
        if (s->hFile && s->hFile != INVALID_HANDLE_VALUE) CloseHandle(s->hFile);
        if (s->temp_path[0]) DeleteFileW(s->temp_path);
        HeapFree(GetProcessHeap(), 0, s);
    }
    return r;
}

/* Ask the recv thread to fetch this item.  Waits for any earlier (possibly
   abandoned) transfer to finish, so there is only ever one in flight. */
static BOOL fcs_start_request(FileContentsStream *s)
{
    for (;;) {
        BOOL active;
        EnterCriticalSection(&g_xfer_cs);
        active = g_xfer_active ? TRUE : FALSE;
        LeaveCriticalSection(&g_xfer_cs);
        if (!active) break;
        WaitForSingleObject(g_xfer_event, 200);
    }

    EnterCriticalSection(&g_xfer_cs);
    ResetEvent(g_xfer_event);
    ResetEvent(g_xfer_start);
    g_xfer_active  = 1;
    g_xfer_done    = 0;
    g_xfer_error   = 0;
    g_xfer_written = 0;
    g_xfer_total   = s->declared_size;
    g_xfer_path[0] = L'\0';
    LeaveCriticalSection(&g_xfer_cs);

    g_file_req_idx = s->index;
    InterlockedExchange(&g_file_req_pending, 1);
    s->started = 1;
    return TRUE;
}

/* Wait for the recv thread to create the temp file and open it for reading. */
static BOOL fcs_open_temp(FileContentsStream *s)
{
    wchar_t path[MAX_PATH];
    int error;

    path[0] = L'\0';
    WaitForSingleObject(g_xfer_start, 120000);

    EnterCriticalSection(&g_xfer_cs);
    error = g_xfer_error;
    if (g_xfer_path[0]) wcscpy_s(path, MAX_PATH, g_xfer_path);
    LeaveCriticalSection(&g_xfer_cs);

    if (error || !path[0]) return FALSE;

    s->hFile = CreateFileW(path, GENERIC_READ,
                           FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE,
                           NULL, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL);
    if (s->hFile == INVALID_HANDLE_VALUE) return FALSE;
    wcscpy_s(s->temp_path, MAX_PATH, path);
    return TRUE;
}

static HRESULT STDMETHODCALLTYPE FCS_Read(IStream *this, void *pv, ULONG cb, ULONG *pcbRead)
{
    FileContentsStream *s = (FileContentsStream *)this;
    DWORD got = 0;

    if (pcbRead) *pcbRead = 0;
    if (cb == 0) return S_OK;

    if (!s->started) {
        if (!fcs_start_request(s)) return E_FAIL;
        if (!fcs_open_temp(s)) return E_FAIL;
    }
    if (!s->hFile || s->hFile == INVALID_HANDLE_VALUE) return E_FAIL;

    for (;;) {
        UINT64 avail;
        int done, error;

        EnterCriticalSection(&g_xfer_cs);
        avail = g_xfer_written;
        done  = g_xfer_done;
        error = g_xfer_error;
        LeaveCriticalSection(&g_xfer_cs);

        if (s->pos < avail) {
            UINT64 n = avail - s->pos;
            LARGE_INTEGER off;
            if (n > cb) n = cb;
            off.QuadPart = (LONGLONG)s->pos;
            if (!SetFilePointerEx(s->hFile, off, NULL, FILE_BEGIN)) return E_FAIL;
            if (!ReadFile(s->hFile, pv, (DWORD)n, &got, NULL)) return E_FAIL;
            s->pos += got;
            if (pcbRead) *pcbRead = got;
            return got ? S_OK : E_FAIL;
        }

        if (done) {
            if (error) return E_FAIL;
            return S_FALSE;          /* clean end of stream */
        }

        WaitForSingleObject(g_xfer_event, 1000);
    }
}

static HRESULT STDMETHODCALLTYPE FCS_Write(IStream *this, const void *pv, ULONG cb, ULONG *pcbWritten)
{
    (void)this; (void)pv; (void)cb;
    if (pcbWritten) *pcbWritten = 0;
    return STG_E_ACCESSDENIED;
}

static HRESULT STDMETHODCALLTYPE FCS_Seek(IStream *this, LARGE_INTEGER dlibMove,
                                          DWORD dwOrigin, ULARGE_INTEGER *plibNewPosition)
{
    FileContentsStream *s = (FileContentsStream *)this;
    LONGLONG base;
    LONGLONG np;

    switch (dwOrigin) {
    case STREAM_SEEK_SET: base = 0; break;
    case STREAM_SEEK_CUR: base = (LONGLONG)s->pos; break;
    case STREAM_SEEK_END: base = (LONGLONG)s->declared_size; break;
    default: return STG_E_INVALIDFUNCTION;
    }

    np = base + dlibMove.QuadPart;
    if (np < 0) return STG_E_INVALIDFUNCTION;

    s->pos = (UINT64)np;
    if (plibNewPosition) plibNewPosition->QuadPart = (ULONGLONG)np;
    return S_OK;
}

static HRESULT STDMETHODCALLTYPE FCS_SetSize(IStream *this, ULARGE_INTEGER libNewSize)
{
    (void)this; (void)libNewSize;
    return E_NOTIMPL;
}

static HRESULT STDMETHODCALLTYPE FCS_CopyTo(IStream *this, IStream *pstm, ULARGE_INTEGER cb,
                                            ULARGE_INTEGER *pcbRead, ULARGE_INTEGER *pcbWritten)
{
    FileContentsStream *s = (FileContentsStream *)this;
    BYTE buf[64 * 1024];
    UINT64 left = cb.QuadPart;
    UINT64 rd = 0, wr = 0;

    if (pcbRead) pcbRead->QuadPart = 0;
    if (pcbWritten) pcbWritten->QuadPart = 0;

    /* cb == 0 means "copy to the end of the stream". */
    if (cb.QuadPart == 0) {
        if (s->declared_size > s->pos) left = s->declared_size - s->pos;
        else left = ~(UINT64)0;   /* size unknown/streaming: read until S_FALSE */
    }

    while (left > 0) {
        ULONG want = left > sizeof(buf) ? (ULONG)sizeof(buf) : (ULONG)left;
        ULONG got = 0, written = 0;
        HRESULT hr = FCS_Read(this, buf, want, &got);
        if (FAILED(hr)) return hr;
        if (got == 0) break;
        rd += got;
        hr = pstm->lpVtbl->Write(pstm, buf, got, &written);
        if (FAILED(hr)) return hr;
        wr += written;
        left -= got;
        if (hr == S_FALSE) break;
    }

    if (pcbRead) pcbRead->QuadPart = rd;
    if (pcbWritten) pcbWritten->QuadPart = wr;
    return S_OK;
}

static HRESULT STDMETHODCALLTYPE FCS_Commit(IStream *this, DWORD grfCommitFlags)
{
    (void)this; (void)grfCommitFlags;
    return S_OK;
}

static HRESULT STDMETHODCALLTYPE FCS_Revert(IStream *this)
{
    (void)this;
    return E_NOTIMPL;
}

static HRESULT STDMETHODCALLTYPE FCS_LockRegion(IStream *this, ULARGE_INTEGER libOffset,
                                                ULARGE_INTEGER cb, DWORD dwLockType)
{
    (void)this; (void)libOffset; (void)cb; (void)dwLockType;
    return E_NOTIMPL;
}

static HRESULT STDMETHODCALLTYPE FCS_UnlockRegion(IStream *this, ULARGE_INTEGER libOffset,
                                                  ULARGE_INTEGER cb, DWORD dwLockType)
{
    (void)this; (void)libOffset; (void)cb; (void)dwLockType;
    return E_NOTIMPL;
}

static HRESULT STDMETHODCALLTYPE FCS_Stat(IStream *this, STATSTG *pstatstg, DWORD grfStatFlag)
{
    FileContentsStream *s = (FileContentsStream *)this;
    (void)grfStatFlag;
    if (!pstatstg) return E_INVALIDARG;
    ZeroMemory(pstatstg, sizeof(*pstatstg));
    pstatstg->type = STGTY_STREAM;
    pstatstg->cbSize.QuadPart = s->declared_size;
    return S_OK;
}

static HRESULT STDMETHODCALLTYPE FCS_Clone(IStream *this, IStream **ppstm)
{
    (void)this;
    if (ppstm) *ppstm = NULL;
    return E_NOTIMPL;
}

/* ---------- IEnumFORMATETC ---------- */

typedef struct {
    IEnumFORMATETCVtbl *lpVtbl;
    LONG ref;
    FORMATETC *items;
    int count;
    int pos;
} AsbEnum;

static HRESULT STDMETHODCALLTYPE EN_QueryInterface(IEnumFORMATETC *this, REFIID riid, void **ppv)
{
    if (!ppv) return E_INVALIDARG;
    if (IsEqualIID(riid, &IID_IUnknown) || IsEqualIID(riid, &IID_IEnumFORMATETC)) {
        *ppv = this;
        this->lpVtbl->AddRef(this);
        return S_OK;
    }
    *ppv = NULL;
    return E_NOINTERFACE;
}

static ULONG STDMETHODCALLTYPE EN_AddRef(IEnumFORMATETC *this)
{
    return (ULONG)InterlockedIncrement(&((AsbEnum *)this)->ref);
}

static ULONG STDMETHODCALLTYPE EN_Release(IEnumFORMATETC *this)
{
    AsbEnum *e = (AsbEnum *)this;
    ULONG r = (ULONG)InterlockedDecrement(&e->ref);
    if (r == 0) {
        if (e->items) HeapFree(GetProcessHeap(), 0, e->items);
        HeapFree(GetProcessHeap(), 0, e);
    }
    return r;
}

static HRESULT STDMETHODCALLTYPE EN_Next(IEnumFORMATETC *this, ULONG celt,
                                         FORMATETC *rgelt, ULONG *pceltFetched)
{
    AsbEnum *e = (AsbEnum *)this;
    ULONG n = 0;

    if (!rgelt) return E_INVALIDARG;
    while (n < celt && e->pos < e->count)
        rgelt[n++] = e->items[e->pos++];
    if (pceltFetched) *pceltFetched = n;
    return (n == celt) ? S_OK : S_FALSE;
}

static HRESULT STDMETHODCALLTYPE EN_Skip(IEnumFORMATETC *this, ULONG celt)
{
    AsbEnum *e = (AsbEnum *)this;
    e->pos += (int)celt;
    if (e->pos > e->count) e->pos = e->count;
    return S_OK;
}

static HRESULT STDMETHODCALLTYPE EN_Reset(IEnumFORMATETC *this)
{
    ((AsbEnum *)this)->pos = 0;
    return S_OK;
}

static HRESULT STDMETHODCALLTYPE EN_Clone(IEnumFORMATETC *this, IEnumFORMATETC **ppenum)
{
    AsbEnum *e = (AsbEnum *)this;
    AsbEnum *c;

    if (!ppenum) return E_INVALIDARG;
    *ppenum = NULL;
    c = (AsbEnum *)HeapAlloc(GetProcessHeap(), HEAP_ZERO_MEMORY, sizeof(AsbEnum));
    if (!c) return E_OUTOFMEMORY;
    c->items = (FORMATETC *)HeapAlloc(GetProcessHeap(), 0, sizeof(FORMATETC) * e->count);
    if (!c->items) { HeapFree(GetProcessHeap(), 0, c); return E_OUTOFMEMORY; }
    memcpy(c->items, e->items, sizeof(FORMATETC) * e->count);
    c->lpVtbl = &EN_Vtbl;
    c->ref = 1;
    c->count = e->count;
    c->pos = e->pos;
    *ppenum = (IEnumFORMATETC *)c;
    return S_OK;
}

/* ---------- IDataObject ---------- */

static HRESULT STDMETHODCALLTYPE DO_QueryInterface(IDataObject *this, REFIID riid, void **ppv)
{
    if (!ppv) return E_INVALIDARG;
    if (IsEqualIID(riid, &IID_IUnknown) || IsEqualIID(riid, &IID_IDataObject)) {
        *ppv = this;
        this->lpVtbl->AddRef(this);
        return S_OK;
    }
    *ppv = NULL;
    return E_NOINTERFACE;
}

static ULONG STDMETHODCALLTYPE DO_AddRef(IDataObject *this)
{
    return (ULONG)InterlockedIncrement(&((AsbDO *)this)->ref);
}

static ULONG STDMETHODCALLTYPE DO_Release(IDataObject *this)
{
    AsbDO *d = (AsbDO *)this;
    ULONG r = (ULONG)InterlockedDecrement(&d->ref);
    if (r == 0) {
        int i;
        for (i = 0; i < d->small_count; i++)
            if (d->smalls[i].h) GlobalFree(d->smalls[i].h);
        if (d->meta) HeapFree(GetProcessHeap(), 0, d->meta);
        HeapFree(GetProcessHeap(), 0, d);
    }
    return r;
}

static HRESULT STDMETHODCALLTYPE DO_GetData(IDataObject *this, FORMATETC *pformatetc,
                                            STGMEDIUM *pmedium)
{
    AsbDO *d = (AsbDO *)this;
    int i;

    if (!pformatetc || !pmedium) return E_INVALIDARG;
    ZeroMemory(pmedium, sizeof(*pmedium));
    if (pformatetc->dwAspect != DVASPECT_CONTENT) return DV_E_DVASPECT;

    if (pformatetc->cfFormat == g_cf_file_desc && (pformatetc->tymed & TYMED_HGLOBAL)) {
        SIZE_T size = sizeof(FILEGROUPDESCRIPTORW) +
                      (d->meta_count > 0
                           ? (SIZE_T)(d->meta_count - 1) * sizeof(FILEDESCRIPTORW)
                           : 0);
        HGLOBAL h = GlobalAlloc(GMEM_MOVEABLE | GMEM_ZEROINIT, size);
        FILEGROUPDESCRIPTORW *fgd;

        if (!h) return E_OUTOFMEMORY;
        fgd = (FILEGROUPDESCRIPTORW *)GlobalLock(h);
        if (!fgd) { GlobalFree(h); return E_OUTOFMEMORY; }
        fgd->cItems = (UINT)d->meta_count;
        for (i = 0; i < d->meta_count; i++) {
            FILEDESCRIPTORW *fd = &fgd->fgd[i];
            fd->dwFlags = FD_ATTRIBUTES |
                          (d->meta[i].is_dir ? 0 : (FD_FILESIZE | FD_PROGRESSUI));
            fd->dwFileAttributes = d->meta[i].is_dir
                                       ? FILE_ATTRIBUTE_DIRECTORY
                                       : (d->meta[i].attrs & 0xFFFF);
            fd->nFileSizeLow  = (DWORD)(d->meta[i].size & 0xFFFFFFFF);
            fd->nFileSizeHigh = (DWORD)(d->meta[i].size >> 32);
            lstrcpynW(fd->cFileName, d->meta[i].name, ARRAYSIZE(fd->cFileName));
        }
        GlobalUnlock(h);
        pmedium->tymed = TYMED_HGLOBAL;
        pmedium->hGlobal = h;
        return S_OK;
    }

    if (pformatetc->cfFormat == g_cf_file_contents && (pformatetc->tymed & TYMED_ISTREAM)) {
        FileContentsStream *s;
        i = pformatetc->lindex;
        if (i < 0 || i >= d->meta_count) return DV_E_LINDEX;
        s = (FileContentsStream *)HeapAlloc(GetProcessHeap(), HEAP_ZERO_MEMORY,
                                            sizeof(FileContentsStream));
        if (!s) return E_OUTOFMEMORY;
        s->lpVtbl = &FCS_Vtbl;
        s->ref = 1;
        s->index = i;
        s->declared_size = d->meta[i].size;
        s->hFile = INVALID_HANDLE_VALUE;
        pmedium->tymed = TYMED_ISTREAM;
        pmedium->pstm = (IStream *)s;
        return S_OK;
    }

    for (i = 0; i < d->small_count; i++) {
        if (d->smalls[i].fmt == pformatetc->cfFormat && (pformatetc->tymed & TYMED_HGLOBAL)) {
            SIZE_T sz = d->smalls[i].size;
            HGLOBAL h = GlobalAlloc(GMEM_MOVEABLE, sz);
            void *src, *dst;

            if (!h) return E_OUTOFMEMORY;
            src = GlobalLock(d->smalls[i].h);
            dst = GlobalLock(h);
            if (src && dst) memcpy(dst, src, sz);
            if (src) GlobalUnlock(d->smalls[i].h);
            if (dst) GlobalUnlock(h);
            if (!src || !dst) { GlobalFree(h); return E_OUTOFMEMORY; }
            pmedium->tymed = TYMED_HGLOBAL;
            pmedium->hGlobal = h;
            return S_OK;
        }
    }

    return DV_E_FORMATETC;
}

static HRESULT STDMETHODCALLTYPE DO_GetDataHere(IDataObject *this, FORMATETC *pformatetc,
                                                STGMEDIUM *pmedium)
{
    (void)this; (void)pformatetc; (void)pmedium;
    return E_NOTIMPL;
}

static HRESULT STDMETHODCALLTYPE DO_QueryGetData(IDataObject *this, FORMATETC *pformatetc)
{
    AsbDO *d = (AsbDO *)this;
    int i;

    if (!pformatetc) return E_INVALIDARG;
    if (pformatetc->dwAspect != DVASPECT_CONTENT) return DV_E_DVASPECT;

    if (pformatetc->cfFormat == g_cf_file_desc && (pformatetc->tymed & TYMED_HGLOBAL))
        return S_OK;

    if (pformatetc->cfFormat == g_cf_file_contents && (pformatetc->tymed & TYMED_ISTREAM)) {
        if (pformatetc->lindex < 0 || pformatetc->lindex >= d->meta_count)
            return DV_E_LINDEX;
        return S_OK;
    }

    for (i = 0; i < d->small_count; i++) {
        if (pformatetc->cfFormat == d->smalls[i].fmt && (pformatetc->tymed & TYMED_HGLOBAL))
            return S_OK;
    }

    return DV_E_FORMATETC;
}

static HRESULT STDMETHODCALLTYPE DO_GetCanonicalFormatEtc(IDataObject *this,
                                                          FORMATETC *pformatectIn,
                                                          FORMATETC *pformatetcOut)
{
    (void)this;
    if (!pformatectIn || !pformatetcOut) return E_INVALIDARG;
    *pformatetcOut = *pformatectIn;
    pformatetcOut->ptd = NULL;
    return DATA_S_SAMEFORMATETC;
}

static HRESULT STDMETHODCALLTYPE DO_SetData(IDataObject *this, FORMATETC *pformatetc,
                                            STGMEDIUM *pmedium, BOOL fRelease)
{
    (void)this; (void)pformatetc; (void)pmedium; (void)fRelease;
    return E_NOTIMPL;
}

static HRESULT STDMETHODCALLTYPE DO_EnumFormatEtc(IDataObject *this, DWORD dwDirection,
                                                  IEnumFORMATETC **ppenumFormatEtc)
{
    AsbDO *d = (AsbDO *)this;
    AsbEnum *e;
    FORMATETC *items;
    int total, i, n = 0;

    if (!ppenumFormatEtc) return E_INVALIDARG;
    *ppenumFormatEtc = NULL;
    if (dwDirection != DATADIR_GET) return E_NOTIMPL;

    total = 1 + d->meta_count + d->small_count;
    items = (FORMATETC *)HeapAlloc(GetProcessHeap(), 0, sizeof(FORMATETC) * total);
    if (!items) return E_OUTOFMEMORY;

    ZeroMemory(&items[n], sizeof(FORMATETC));
    items[n].cfFormat = (CLIPFORMAT)g_cf_file_desc;
    items[n].dwAspect = DVASPECT_CONTENT;
    items[n].lindex   = -1;
    items[n].tymed    = TYMED_HGLOBAL;
    n++;

    for (i = 0; i < d->meta_count; i++) {
        ZeroMemory(&items[n], sizeof(FORMATETC));
        items[n].cfFormat = (CLIPFORMAT)g_cf_file_contents;
        items[n].dwAspect = DVASPECT_CONTENT;
        items[n].lindex   = i;
        items[n].tymed    = TYMED_ISTREAM;
        n++;
    }

    for (i = 0; i < d->small_count; i++) {
        ZeroMemory(&items[n], sizeof(FORMATETC));
        items[n].cfFormat = (CLIPFORMAT)d->smalls[i].fmt;
        items[n].dwAspect = DVASPECT_CONTENT;
        items[n].lindex   = -1;
        items[n].tymed    = TYMED_HGLOBAL;
        n++;
    }

    e = (AsbEnum *)HeapAlloc(GetProcessHeap(), HEAP_ZERO_MEMORY, sizeof(AsbEnum));
    if (!e) { HeapFree(GetProcessHeap(), 0, items); return E_OUTOFMEMORY; }
    e->lpVtbl = &EN_Vtbl;
    e->ref = 1;
    e->items = items;
    e->count = n;
    *ppenumFormatEtc = (IEnumFORMATETC *)e;
    return S_OK;
}

static HRESULT STDMETHODCALLTYPE DO_DAdvise(IDataObject *this, FORMATETC *pformatetc,
                                            DWORD advf, IAdviseSink *pAdvSink,
                                            DWORD *pdwConnection)
{
    (void)this; (void)pformatetc; (void)advf; (void)pAdvSink;
    if (pdwConnection) *pdwConnection = 0;
    return OLE_E_ADVISENOTSUPPORTED;
}

static HRESULT STDMETHODCALLTYPE DO_DUnadvise(IDataObject *this, DWORD dwConnection)
{
    (void)this; (void)dwConnection;
    return OLE_E_ADVISENOTSUPPORTED;
}

static HRESULT STDMETHODCALLTYPE DO_EnumDAdvise(IDataObject *this, IEnumSTATDATA **ppenumAdvise)
{
    (void)this;
    if (ppenumAdvise) *ppenumAdvise = NULL;
    return OLE_E_ADVISENOTSUPPORTED;
}

static IStreamVtbl FCS_Vtbl = {
    FCS_QueryInterface, FCS_AddRef, FCS_Release,
    FCS_Read, FCS_Write, FCS_Seek, FCS_SetSize, FCS_CopyTo, FCS_Commit, FCS_Revert,
    FCS_LockRegion, FCS_UnlockRegion, FCS_Stat, FCS_Clone
};

static IEnumFORMATETCVtbl EN_Vtbl = {
    EN_QueryInterface, EN_AddRef, EN_Release,
    EN_Next, EN_Skip, EN_Reset, EN_Clone
};

static IDataObjectVtbl DO_Vtbl = {
    DO_QueryInterface, DO_AddRef, DO_Release,
    DO_GetData, DO_GetDataHere, DO_QueryGetData, DO_GetCanonicalFormatEtc,
    DO_SetData, DO_EnumFormatEtc, DO_DAdvise, DO_DUnadvise, DO_EnumDAdvise
};

/* Build a data object from the metadata that came with the current list. */
static AsbDO *clip_build_data_object(void)
{
    AsbDO *d;
    int i;

    d = (AsbDO *)HeapAlloc(GetProcessHeap(), HEAP_ZERO_MEMORY, sizeof(AsbDO));
    if (!d) return NULL;
    d->lpVtbl = &DO_Vtbl;
    d->ref = 1;

    d->meta = (FileMeta *)HeapAlloc(GetProcessHeap(), 0,
                                    sizeof(FileMeta) * (size_t)g_file_meta_count);
    if (!d->meta) { HeapFree(GetProcessHeap(), 0, d); return NULL; }
    memcpy(d->meta, g_file_meta, sizeof(FileMeta) * (size_t)g_file_meta_count);
    d->meta_count = g_file_meta_count;

    for (i = 0; i < g_clip_fmt_count && d->small_count < SMALL_MAX; i++) {
        if (g_clip_fmts[i].is_hdrop) continue;
        if (!g_clip_fmts[i].data || g_clip_fmts[i].data_size == 0) continue;
        {
            HGLOBAL h = GlobalAlloc(GMEM_MOVEABLE, g_clip_fmts[i].data_size);
            void *p;
            if (!h) continue;
            p = GlobalLock(h);
            if (!p) { GlobalFree(h); continue; }
            memcpy(p, g_clip_fmts[i].data, g_clip_fmts[i].data_size);
            GlobalUnlock(h);
            d->smalls[d->small_count].fmt = g_clip_fmts[i].local_id;
            d->smalls[d->small_count].h = h;
            d->smalls[d->small_count].size = g_clip_fmts[i].data_size;
            d->small_count++;
        }
    }

    return d;
}

static void clip_apply_format_list(void)
{
    int i;
    BOOL has_nonfile = FALSE;
    LONG gen;

    if (g_clip_fmt_count == 0) return;

    /* The recv thread may be parsing a newer list; keep the shared format
       table stable while it is applied. */
    EnterCriticalSection(&g_state_cs);

    gen = g_list_gen;

    InterlockedExchange(&g_suppress, 1);

    /* Wipe the staging folder for this list before the file fetch starts. */
    clip_remove_dir_recursive(g_clip_temp_dir);
    CreateDirectoryW(g_clip_temp_dir, NULL);

#ifndef ASB_HARNESS
    /* Lazy path: advertise the files natively (FileGroupDescriptorW +
       FileContents) so nothing is downloaded until the user pastes.  The data
       object also carries the small formats, so the win32 path below is only
       used when there is no file metadata (old host) or OLE fails. */
    if (g_file_meta_count > 0) {
        AsbDO *d = clip_build_data_object();
        if (d) {
            HRESULT hr = OleSetClipboard((IDataObject *)d);
            d->lpVtbl->Release((IDataObject *)d);   /* OLE keeps its own ref */

            if (SUCCEEDED(hr)) {
                g_applied_gen = gen;
                g_applied_seq = (LONG)GetClipboardSequenceNumber();
                g_applied_has_nonfile = 1;
                clip_log("Advertised %d file(s) via FileContents (lazy).",
                         g_file_meta_count);
                clip_free_pending();
                LeaveCriticalSection(&g_state_cs);
                return;
            }
            clip_log("OleSetClipboard failed (0x%08lX); falling back to eager files.",
                     (unsigned long)hr);
        } else {
            clip_log("Failed to build file data object; falling back to eager files.");
        }
    }
#endif

    /* Eager path: apply the small (non-file) formats now; the file list is
       added by clip_add_files_to_clipboard once it has downloaded. */
    for (i = 0; i < g_clip_fmt_count; i++) {
        if (g_clip_fmts[i].is_hdrop) continue;
        if (g_clip_fmts[i].data && g_clip_fmts[i].data_size > 0) {
            if (!has_nonfile) {
                if (!OpenClipboard(g_msg_hwnd)) {
                    clip_log("clip_apply_format_list: OpenClipboard failed (%lu).", GetLastError());
                    break;
                }
                EmptyClipboard();
            }
            {
                HGLOBAL hMem = GlobalAlloc(GMEM_MOVEABLE, g_clip_fmts[i].data_size);
                if (hMem) {
                    void *ptr = GlobalLock(hMem);
                    if (ptr) {
                        memcpy(ptr, g_clip_fmts[i].data, g_clip_fmts[i].data_size);
                        GlobalUnlock(hMem);
                        SetClipboardData(g_clip_fmts[i].local_id, hMem);
                    } else {
                        GlobalFree(hMem);
                    }
                }
            }
            has_nonfile = TRUE;
        }
    }
    if (has_nonfile) CloseClipboard();

    g_applied_gen = gen;
    g_applied_seq = (LONG)GetClipboardSequenceNumber();
    g_applied_has_nonfile = has_nonfile ? 1 : 0;

    clip_log("Applied %d formats to clipboard (files pending download).",
             g_clip_fmt_count);
    clip_free_pending();
    LeaveCriticalSection(&g_state_cs);

    /* Eager fallback (old host, or OLE failed): prefetch CF_HDROP in the
       background. No clipboard is held open while the files download. */
    for (i = 0; i < g_clip_fmt_count; i++) {
        if (g_clip_fmts[i].is_hdrop) {
            ClipHeader hdr;
            BOOL sent;
            g_fetch_gen = gen;
            g_file_fetch_active = 1;
            hdr.magic = CLIP_MAGIC;
            hdr.msg_type = CLIP_MSG_FORMAT_DATA_REQ;
            hdr.format = g_clip_fmts[i].remote_id;
            hdr.data_size = 0;
            EnterCriticalSection(&g_send_cs);
            sent = send_all_locked(&hdr, sizeof(hdr));
            LeaveCriticalSection(&g_send_cs);
            if (sent)
                clip_log("Fetching files in background (deferred download started).");
            else
                clip_log("File fetch failed: host socket is closed.");
            break;
        }
    }
}

/* Files for the current list have finished downloading: hand them to the
   clipboard now that they are complete, so a paste never blocks. */
static void clip_add_files_to_clipboard(void)
{
    HGLOBAL hDrop;
    LONG gen;

    EnterCriticalSection(&g_state_cs);

    gen = g_fetch_gen;
    if (gen != g_list_gen) {
        clip_log("File fetch completed for a superseded list - ignoring.");
        LeaveCriticalSection(&g_state_cs);
        return;
    }
    g_file_fetch_active = 0;

    if ((LONG)GetClipboardSequenceNumber() != g_applied_seq) {
        clip_log("Clipboard changed while files were downloading - not overwriting.");
        LeaveCriticalSection(&g_state_cs);
        return;
    }

    hDrop = clip_build_hdrop_from_temp();
    if (hDrop) {
        if (OpenClipboard(g_msg_hwnd)) {
            if (!g_applied_has_nonfile) EmptyClipboard();
            SetClipboardData(CF_HDROP, hDrop);
            CloseClipboard();
            g_applied_seq = (LONG)GetClipboardSequenceNumber();
            clip_log("Files ready in clipboard (CF_HDROP added).");
        } else {
            clip_log("clip_add_files: OpenClipboard failed (%lu).", GetLastError());
            GlobalFree(hDrop);
        }
    } else {
        clip_log("File fetch completed but produced no files.");
    }

    LeaveCriticalSection(&g_state_cs);
}

/* ---- Message window for clipboard monitoring ---- */

static LRESULT CALLBACK clip_msg_wnd_proc(HWND hwnd, UINT msg, WPARAM wp, LPARAM lp)
{
    switch (msg) {
    case WM_CLIP_APPLY_FMTS:
        clip_log("WM_CLIP_APPLY_FMTS — applying fetched data.");
        clip_apply_format_list();
        return 0;
    case WM_CLIP_ADD_FILES:
        clip_log("WM_CLIP_ADD_FILES — adding downloaded files.");
        clip_add_files_to_clipboard();
        return 0;
    case WM_RENDERFORMAT:
        /* Kept for compatibility; files are no longer delayed. */
        return 0;
    }
    return DefWindowProcW(hwnd, msg, wp, lp);
}

static void switch_to_input_desktop(void)
{
    HDESK desk = OpenInputDesktop(0, FALSE, GENERIC_ALL);
    if (desk) {
        SetThreadDesktop(desk);
        CloseDesktop(desk);
    }
}

static DWORD WINAPI msg_window_thread(LPVOID param)
{
    WNDCLASSEXW wc;
    MSG msg;
    (void)param;

    /* Must be on the interactive desktop to access the user's clipboard */
    switch_to_input_desktop();
    OleInitialize(NULL);

    ZeroMemory(&wc, sizeof(wc));
    wc.cbSize        = sizeof(wc);
    wc.lpfnWndProc   = clip_msg_wnd_proc;
    wc.hInstance     = GetModuleHandleW(NULL);
    wc.lpszClassName = L"AppSandboxClipHelper";
    RegisterClassExW(&wc);

    g_msg_hwnd = CreateWindowExW(0, L"AppSandboxClipHelper", NULL,
                                  0, 0, 0, 0, 0, HWND_MESSAGE,
                                  NULL, GetModuleHandleW(NULL), NULL);
    if (!g_msg_hwnd) {
        clip_log("Failed to create message window (%lu).", GetLastError());
        return 1;
    }

    clip_log("Message window created (delayed-render clipboard owner).");

    while (GetMessageW(&msg, NULL, 0, 0) > 0) {
        TranslateMessage(&msg);
        DispatchMessageW(&msg);
    }

    DestroyWindow(g_msg_hwnd);
    g_msg_hwnd = NULL;
    return 0;
}

/* Receive and write a single FILE_DATA message to disk. */
static BOOL clip_recv_file_data(AsbConn *s, const ClipHeader *hdr)
{
    ClipFileInfo fi;
    wchar_t rel_path[MAX_PATH], full_path[MAX_PATH];

    if (hdr->data_size < sizeof(fi)) return FALSE;
    if (!recv_exact(s, &fi, sizeof(fi))) return FALSE;

    if (fi.path_len == 0 || fi.path_len > (MAX_PATH - 1) * sizeof(wchar_t)) {
        UINT32 skip_hdr = hdr->data_size - (UINT32)sizeof(fi);
        BYTE skip[4096];
        while (skip_hdr > 0) {
            int chunk = skip_hdr > 4096 ? 4096 : (int)skip_hdr;
            if (!recv_exact(s, skip, chunk)) return FALSE;
            skip_hdr -= chunk;
        }
        { UINT64 rem = fi.file_size;
          while (rem > 0) { int c = rem > 4096 ? 4096 : (int)rem;
          if (!recv_exact(s, skip, c)) return FALSE; rem -= c; } }
        return TRUE;
    }

    if (!recv_exact(s, rel_path, (int)fi.path_len)) return FALSE;
    rel_path[fi.path_len / sizeof(wchar_t)] = L'\0';

    if (!clip_path_is_safe(rel_path)) {
        BYTE skip[4096];
        UINT64 rem = fi.file_size;
        clip_log("Rejected unsafe path.");
        while (rem > 0) { int c = rem > 4096 ? 4096 : (int)rem;
          if (!recv_exact(s, skip, c)) return FALSE; rem -= c; }
        return TRUE;
    }

    swprintf_s(full_path, MAX_PATH, L"%s\\%s", g_clip_temp_dir, rel_path);

    if (fi.is_directory) {
        clip_ensure_parent_dir(full_path);
        CreateDirectoryW(full_path, NULL);
    } else {
        HANDLE hFile;
        BYTE *chunk;
        clip_ensure_parent_dir(full_path);
        chunk = (BYTE *)HeapAlloc(GetProcessHeap(), 0, CLIP_FILE_CHUNK);
        if (!chunk) return FALSE;
        hFile = CreateFileW(full_path, GENERIC_WRITE, 0, NULL,
                            CREATE_ALWAYS, FILE_ATTRIBUTE_NORMAL, NULL);
        if (hFile != INVALID_HANDLE_VALUE) {
            UINT64 remaining = fi.file_size;
            while (remaining > 0) {
                DWORD to_read = remaining > CLIP_FILE_CHUNK ? CLIP_FILE_CHUNK : (DWORD)remaining;
                DWORD written;
                if (!recv_exact(s, chunk, (int)to_read)) { HeapFree(GetProcessHeap(), 0, chunk); CloseHandle(hFile); return FALSE; }
                WriteFile(hFile, chunk, to_read, &written, NULL);
                remaining -= to_read;
            }
            CloseHandle(hFile);
        } else {
            UINT64 remaining = fi.file_size;
            while (remaining > 0) {
                int c = remaining > CLIP_FILE_CHUNK ? CLIP_FILE_CHUNK : (int)remaining;
                if (!recv_exact(s, chunk, c)) { HeapFree(GetProcessHeap(), 0, chunk); return FALSE; }
                remaining -= c;
            }
        }
        HeapFree(GetProcessHeap(), 0, chunk);
    }
    return TRUE;
}

/* ---- Recv thread: delayed rendering protocol ---- */

static DWORD WINAPI recv_thread_proc(LPVOID param)
{
    AsbConn *s = (AsbConn *)param;
    ClipHeader hdr;

    clip_log("Recv thread started.");

    while (1) {
        /* If the apply is waiting only for file metadata, release it as soon
           as the metadata arrives (or the old-host timeout expires). */
        if (g_apply_pending &&
            (g_file_meta_count > 0 || GetTickCount64() >= g_meta_deadline)) {
            InterlockedExchange(&g_apply_pending, 0);
            if (g_msg_hwnd)
                PostMessageW(g_msg_hwnd, WM_CLIP_APPLY_FMTS, 0, 0);
        }

        /* Serve a pending on-demand file request (FileContents paste).
           The bytes are written to a temp file as they arrive; the waiting
           IStream drains it, so the shell's progress dialog advances. */
        if (g_file_req_pending) {
            ClipHeader rhdr;
            ClipHeader r;
            ClipFileInfo fi;
            UINT32 idx = (UINT32)g_file_req_idx;
            BOOL ok = TRUE;

            EnterCriticalSection(&g_xfer_cs);
            g_xfer_written = 0;
            g_xfer_done    = 0;
            g_xfer_error   = 0;
            g_xfer_path[0] = L'\0';
            LeaveCriticalSection(&g_xfer_cs);

            rhdr.magic = CLIP_MAGIC;
            rhdr.msg_type = CLIP_MSG_FILE_DATA_REQ;
            rhdr.format = 0;
            rhdr.data_size = 4;
            EnterCriticalSection(&g_send_cs);
            if (!send_all_locked(&rhdr, sizeof(rhdr)) ||
                !send_all_locked(&idx, 4))
                ok = FALSE;
            LeaveCriticalSection(&g_send_cs);

            if (ok && recv_exact(s, &r, sizeof(r)) && r.magic == CLIP_MAGIC) {
                if (recv_exact(s, &fi, sizeof(fi))) {
                    wchar_t rel[MAX_PATH];
                    rel[0] = L'\0';
                    if (fi.path_len > 0 &&
                        fi.path_len <= (MAX_PATH - 1) * sizeof(wchar_t)) {
                        if (recv_exact(s, rel, (int)fi.path_len))
                            rel[fi.path_len / sizeof(wchar_t)] = L'\0';
                        else
                            ok = FALSE;
                    } else if (fi.path_len > 0) {
                        BYTE skip[4096];
                        UINT32 rem = fi.path_len;
                        while (ok && rem > 0) {
                            int c = rem > 4096 ? 4096 : (int)rem;
                            if (!recv_exact(s, skip, c)) ok = FALSE;
                            rem -= c;
                        }
                    }

                    if (ok) {
                        wchar_t tmp[MAX_PATH];
                        HANDLE hf;

                        CreateDirectoryW(g_clip_temp_dir, NULL);
                        swprintf_s(tmp, MAX_PATH, L"%s\\_fc_%d.tmp",
                                   g_clip_temp_dir, (int)idx);
                        hf = CreateFileW(tmp, GENERIC_WRITE,
                                         FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE,
                                         NULL, CREATE_ALWAYS, FILE_ATTRIBUTE_NORMAL, NULL);
                        if (hf != INVALID_HANDLE_VALUE) {
                            BYTE *chunk = (BYTE *)HeapAlloc(GetProcessHeap(), 0, CLIP_FILE_CHUNK);
                            UINT64 remaining = fi.file_size;

                            EnterCriticalSection(&g_xfer_cs);
                            wcscpy_s(g_xfer_path, MAX_PATH, tmp);
                            g_xfer_total = fi.file_size;
                            LeaveCriticalSection(&g_xfer_cs);
                            SetEvent(g_xfer_start);   /* reader may open it now */

                            while (ok && remaining > 0) {
                                DWORD to_read = remaining > CLIP_FILE_CHUNK
                                                    ? CLIP_FILE_CHUNK
                                                    : (DWORD)remaining;
                                DWORD written = 0;

                                if (!chunk || !recv_exact(s, chunk, (int)to_read)) {
                                    ok = FALSE;
                                    break;
                                }
                                if (!WriteFile(hf, chunk, to_read, &written, NULL) ||
                                    written != to_read) {
                                    ok = FALSE;
                                    break;
                                }
                                EnterCriticalSection(&g_xfer_cs);
                                g_xfer_written += written;
                                LeaveCriticalSection(&g_xfer_cs);
                                SetEvent(g_xfer_event);
                                remaining -= to_read;
                            }

                            if (chunk) HeapFree(GetProcessHeap(), 0, chunk);
                            CloseHandle(hf);
                        } else {
                            ok = FALSE;
                        }
                    }
                } else {
                    ok = FALSE;
                }
            } else {
                ok = FALSE;
            }

            EnterCriticalSection(&g_xfer_cs);
            if (!ok) g_xfer_error = 1;
            g_xfer_done   = 1;
            g_xfer_active = 0;
            LeaveCriticalSection(&g_xfer_cs);
            SetEvent(g_xfer_start);   /* wake a reader that never got a file */
            SetEvent(g_xfer_event);
            InterlockedExchange(&g_file_req_pending, 0);
            continue;
        }

        /* Poll instead of blocking in recv(): a paste can ask for a file at any
           moment, and only this thread can serve it. */
        {
            int pr = asb_poll(s, 50);
            if (pr < 0) break;
            if (pr == 0) continue;
        }

        if (!recv_exact(s, &hdr, sizeof(hdr)))
            break;

        if (hdr.magic != CLIP_MAGIC) {
            clip_log("Bad magic 0x%08X, disconnecting.", hdr.magic);
            break;
        }

        switch (hdr.msg_type) {

        case CLIP_MSG_SYNC_ENABLE: {
            UINT8 flag = 0;
            if (hdr.data_size >= 1) {
                if (!recv_exact(s, &flag, 1)) goto done;
                if (hdr.data_size > 1) {
                    BYTE skip[256];
                    UINT32 rem = hdr.data_size - 1;
                    while (rem > 0) {
                        int c = rem > 256 ? 256 : (int)rem;
                        if (!recv_exact(s, skip, c)) goto done;
                        rem -= c;
                    }
                }
            }
            InterlockedExchange(&g_sync_enabled, flag ? 1 : 0);
            if (flag && g_sync_event) SetEvent(g_sync_event);
            else if (!flag && g_sync_event) ResetEvent(g_sync_event);
            clip_log("SYNC_ENABLE %s", flag ? "ON" : "OFF");
            break;
        }

        case CLIP_MSG_FORMAT_LIST: {
            BYTE buf[16384];
            UINT32 count, i;
            int off;

            if (hdr.data_size > sizeof(buf)) goto done;
            if (hdr.data_size < 4) goto done;
            if (!recv_exact(s, buf, (int)hdr.data_size)) goto done;

            if (!g_sync_enabled) {
                clip_log("FORMAT_LIST ignored (sync disabled).");
                break;
            }

            count = *(UINT32 *)buf;
            if (count > CLIP_MAX_FORMATS) count = CLIP_MAX_FORMATS;
            off = 4;

            /* A new list supersedes any in-flight file fetch. */
            g_file_fetch_active = 0;

            /* Serialize with apply/add-files on the window thread. */
            EnterCriticalSection(&g_state_cs);
            clip_free_pending();
            g_clip_fmt_count = 0;
            for (i = 0; i < count && off + 8 <= (int)hdr.data_size; i++) {
                UINT32 fmt_id   = *(UINT32 *)(buf + off); off += 4;
                UINT32 name_len = *(UINT32 *)(buf + off); off += 4;
                UINT local_id = fmt_id;

                /* off is in [8, data_size] here; reject a name_len that runs
                   past the buffer (or whose signed cast would corrupt off)
                   before the unconditional `off += name_len` advance below. */
                if (name_len > (UINT32)((int)hdr.data_size - off)) break;

                if (name_len > 0 && name_len < 256 && off + (int)name_len <= (int)hdr.data_size) {
                    char name[256];
                    memcpy(name, buf + off, name_len);
                    name[name_len] = '\0';
                    local_id = RegisterClipboardFormatA(name);
                    clip_log("Format '%s' remote=%u local=%u.", name, fmt_id, local_id);
                }
                off += (int)name_len;

                g_clip_fmts[g_clip_fmt_count].local_id = local_id;
                g_clip_fmts[g_clip_fmt_count].remote_id = fmt_id;
                g_clip_fmts[g_clip_fmt_count].data = NULL;
                g_clip_fmts[g_clip_fmt_count].data_size = 0;
                /* CF_HDROP is the file list: fetched in the background after apply. */
                g_clip_fmts[g_clip_fmt_count].is_hdrop =
                    (local_id == CF_HDROP) ? TRUE : FALSE;
                g_clip_fmt_count++;
            }
            /* A new list always starts with no file metadata: the host sends
               it as a separate FILE_LIST right after this message. */
            g_file_meta_count = 0;
            g_list_has_hdrop = 0;
            for (i = 0; i < (UINT32)g_clip_fmt_count; i++) {
                if (g_clip_fmts[i].is_hdrop) { g_list_has_hdrop = 1; break; }
            }
            /* Old hosts never send FILE_LIST; do not wait for them forever. */
            g_meta_deadline = GetTickCount64() + 1000;

            g_list_gen++;
            g_clip_fetch_idx = 0;
            LeaveCriticalSection(&g_state_cs);

            clip_log("Received format list (%u formats); fetching non-file formats...",
                     g_clip_fmt_count);

            /* Temp files are cleaned when the list is applied (or when a
               render starts), never here: a lazy list must not delete the
               files a pending paste might still need. */

            /* Fetch the small formats; CF_HDROP entries are skipped. */
            clip_request_next_format();
            break;
        }

        case CLIP_MSG_FORMAT_DATA_RESP: {
            int idx = g_clip_fetch_idx;

            /* Completion of the background file fetch: the host streams
               FILE_DATA messages and terminates with an empty FORMAT_DATA_RESP
               for CF_HDROP. Wake the window thread to add the files. */
            if (hdr.format == CF_HDROP && g_file_fetch_active) {
                clip_log("Data response for background file fetch (format %u, %u bytes).",
                         hdr.format, hdr.data_size);
                if (hdr.data_size > 0) {
                    BYTE skip[4096];
                    UINT32 rem = hdr.data_size;
                    while (rem > 0) {
                        int c = rem > 4096 ? 4096 : (int)rem;
                        if (!recv_exact(s, skip, c)) goto done;
                        rem -= c;
                    }
                }
                if (g_msg_hwnd)
                    PostMessageW(g_msg_hwnd, WM_CLIP_ADD_FILES, 0, 0);
                clip_log("File fetch complete.");
                break;
            }

            clip_log("Data response for format %u (%u bytes).", hdr.format, hdr.data_size);

            if (idx >= 0 && idx < g_clip_fmt_count) {
                if (hdr.data_size > 0 && hdr.data_size <= CLIP_MAX_PAYLOAD) {
                    BYTE *data = (BYTE *)HeapAlloc(GetProcessHeap(), 0, hdr.data_size);
                    if (data && recv_exact(s, data, (int)hdr.data_size)) {
                        g_clip_fmts[idx].data = data;
                        g_clip_fmts[idx].data_size = hdr.data_size;
                    } else {
                        if (data) HeapFree(GetProcessHeap(), 0, data);
                    }
                }
                g_clip_fetch_idx++;
                clip_request_next_format();
            }
            break;
        }

        case CLIP_MSG_FILE_DATA:
            CreateDirectoryW(g_clip_temp_dir, NULL);
            if (!clip_recv_file_data(s, &hdr)) goto done;
            break;

        case CLIP_MSG_FILE_LIST: {
            /* File metadata for FileContents. Parse into g_file_meta. */
            BYTE *buf = NULL;
            UINT32 count, i, off = 0;
            if (hdr.data_size < 4) break;
            buf = (BYTE *)HeapAlloc(GetProcessHeap(), 0, hdr.data_size);
            if (!buf) break;
            if (!recv_exact(s, buf, (int)hdr.data_size)) { HeapFree(GetProcessHeap(), 0, buf); goto done; }
            count = *(UINT32 *)buf; off = 4;
            if (count > META_MAX) count = META_MAX;
            EnterCriticalSection(&g_state_cs);
            g_file_meta_count = 0;
            for (i = 0; i < count && off + 4 <= (int)hdr.data_size; i++) {
                UINT32 name_len = *(UINT32 *)(buf + off); off += 4;
                if (name_len > (MAX_PATH - 1) * sizeof(wchar_t) || off + (int)name_len + 8 + 4 + 1 > (int)hdr.data_size) break;
                if (name_len > 0) {
                    memcpy(g_file_meta[g_file_meta_count].name, buf + off, name_len);
                    g_file_meta[g_file_meta_count].name[name_len / sizeof(wchar_t)] = L'\0';
                } else {
                    g_file_meta[g_file_meta_count].name[0] = L'\0';
                }
                off += name_len;
                g_file_meta[g_file_meta_count].size = *(UINT64 *)(buf + off); off += 8;
                g_file_meta[g_file_meta_count].attrs = *(UINT32 *)(buf + off); off += 4;
                g_file_meta[g_file_meta_count].is_dir = buf[off++] ? 1 : 0;
                g_file_meta_count++;
            }
            LeaveCriticalSection(&g_state_cs);
            HeapFree(GetProcessHeap(), 0, buf);
            clip_log("Received file metadata (%d entries).", g_file_meta_count);
            break;
        }

        case CLIP_MSG_FILE_DATA_REQ: {
            /* Host? No, this case is guest receiving. Guest doesn't receive this. */
            /* Actually guest sends FILE_DATA_REQ; nothing to do here. */
            if (hdr.data_size > 0) {
                BYTE skip[256]; UINT32 rem = hdr.data_size;
                while (rem > 0) { int c = rem > 256 ? 256 : (int)rem; if (!recv_exact(s, skip, c)) goto done; rem -= c; }
            }
            break;
        }

        default:
            clip_log("Unknown msg_type %u.", hdr.msg_type);
            if (hdr.data_size > 0) {
                BYTE skip[256];
                UINT32 remaining = hdr.data_size;
                while (remaining > 0) {
                    int chunk = remaining > 256 ? 256 : (int)remaining;
                    if (!recv_exact(s, skip, chunk)) goto done;
                    remaining -= chunk;
                }
            }
            break;
        }
    }

done:
    /* Detach the socket before waking a waiting paste: a render that starts
       after this point sends nothing (g_client_sock is NULL) instead of
       blocking for the full timeout on a socket nobody reads. */
    EnterCriticalSection(&g_send_cs);
    g_client_sock = NULL;
    LeaveCriticalSection(&g_send_cs);

    /* Drop any in-flight file fetch if the host goes away. */
    g_file_fetch_active = 0;
    InterlockedExchange(&g_apply_pending, 0);

    /* Unblock a paste that is waiting for bytes we can no longer deliver. */
    EnterCriticalSection(&g_xfer_cs);
    if (g_xfer_active) g_xfer_error = 1;
    g_xfer_done   = 1;
    g_xfer_active = 0;
    LeaveCriticalSection(&g_xfer_cs);
    SetEvent(g_xfer_start);
    SetEvent(g_xfer_event);

    clip_log("Recv thread exiting.");
    return 0;
}

/* ---- Handle one client connection ---- */

static void handle_client(AsbConn *s)
{
    UINT32 ready = CLIP_READY_MAGIC;
    HANDLE recv_th;

    /* Send ready signal */
    if (asb_send(s, &ready, sizeof(ready)) != (int)sizeof(ready)) {
        clip_log("Failed to send ready signal.");
        return;
    }
    clip_log("Sent ready signal to host.");

    g_client_sock = s;

    /* Start recv thread */
    recv_th = CreateThread(NULL, 0, recv_thread_proc, (LPVOID)s, 0, NULL);
    if (!recv_th) {
        clip_log("Failed to create recv thread (%lu).", GetLastError());
        g_client_sock = NULL;
        return;
    }

    /* Wait for recv thread to finish (host disconnected) */
    WaitForSingleObject(recv_th, INFINITE);
    CloseHandle(recv_th);

    g_client_sock = NULL;

    /* Serialize with apply/add-files on the window thread before tearing
       down. */
    EnterCriticalSection(&g_state_cs);
    clip_free_pending();
    g_clip_fmt_count = 0;
    g_file_fetch_active = 0;
    g_file_meta_count = 0;
    g_list_has_hdrop = 0;
    clip_remove_dir_recursive(g_clip_temp_dir);
    LeaveCriticalSection(&g_state_cs);
    clip_log("Client disconnected.");
}

/* ---- Main ---- */

int main(void)
{
    HANDLE msg_th;
    AsbListener *l;

    clip_log("Starting (PID=%lu, session=%lu).",
             GetCurrentProcessId(),
             WTSGetActiveConsoleSessionId());

    InitializeCriticalSection(&g_send_cs);
    InitializeCriticalSection(&g_state_cs);
    InitializeCriticalSection(&g_xfer_cs);
    g_xfer_event = CreateEventW(NULL, FALSE, FALSE, NULL);
    g_xfer_start = CreateEventW(NULL, FALSE, FALSE, NULL);
    g_clip_fetch_idx = 0;
    g_list_gen = 0;
    g_file_fetch_active = 0;

    clip_init_temp_dir();

    g_cf_file_desc = RegisterClipboardFormatW(L"FileGroupDescriptorW");
    g_cf_file_contents = RegisterClipboardFormatW(L"FileContents");

    g_sync_event = CreateEventW(NULL, TRUE, FALSE, CLIP_SYNC_EVENT_NAME);
    if (!g_sync_event)
        clip_log("Warning: failed to create sync event (%lu).", GetLastError());

    /* Start message window thread (clipboard listener) */
    msg_th = CreateThread(NULL, 0, msg_window_thread, NULL, 0, NULL);
    if (!msg_th) {
        clip_log("Failed to create message window thread (%lu).", GetLastError());
        DeleteCriticalSection(&g_send_cs);
        return 1;
    }

    /* Wait a moment for message window to be created */
    Sleep(100);

    if (asb_transport_init() != 0) {
        clip_log("asb_transport_init failed.");
        DeleteCriticalSection(&g_send_cs);
        return 1;
    }

    l = asb_listen(ASB_CH_CLIPBOARD);
    if (!l) {
        clip_log("asb_listen(ASB_CH_CLIPBOARD) failed.");
        DeleteCriticalSection(&g_send_cs);
        return 1;
    }
    clip_log("Listening on clipboard channel (transport=%s).",
             asb_transport_is_ivshmem() ? "ivshmem" : "hyperv");

    /* Accept loop — one client at a time */
    for (;;) {
        AsbConn *c = asb_accept(l, -1);
        if (!c) {
            Sleep(100);
            continue;
        }
        clip_log("Host connected.");
        handle_client(c);
        asb_close(c);
    }
}
