/*
 * Audit and filter SELinux access queries that probe Magisk contexts.
 *
 * Transaction queries are filtered at the direct selinuxfs write handlers,
 * where /sys/fs/selinux/access and /sys/fs/selinux/context still have the
 * original query text.  procattr writes are filtered at selinux_setprocattr().
 * Returning -EINVAL for Magisk contexts matches the clean-policy behavior
 * where the Magisk type/context does not exist.
 */

#include <linux/kernel.h>
#include <linux/printk.h>
#include <linux/sched.h>
#include <linux/fs.h>
#include <linux/vmalloc.h>
#include <linux/err.h>
#include <asm/current.h>
#include <asm-generic/rwonce.h>
#include <uapi/asm-generic/errno.h>
#include <uapi/asm-generic/fcntl.h>
#include <uapi/linux/fs.h>
#include <security.h>
#include <ksyms.h>
#include <hook.h>
#include <kpmodule.h>
#include <kputils.h>

KPM_NAME("selinux_MAF_ST");
KPM_VERSION("v0.0.1");
KPM_LICENSE("GPL v3");
KPM_AUTHOR("Admire, 741afb7");
KPM_DESCRIPTION("Audit and reject Magisk /sys/fs/selinux/access probes");

#define ACCESS_SAMPLE_MAX 256
#define ACCESS_PROBE_SLOTS 32
#define CLEAN_POLICYDB_ALLOC_SIZE 0x4000
#define SELINUX_LEGACY_BLOB_QUERY_MAX VERSION(4, 15, 0)
#define contains_case_literal(s, len, lit) contains_case_lit((s), (len), (lit), sizeof(lit) - 1)

#define MAGISK_POLICY_PATH "/.magisk/selinux/load"
#define MAGISK_POLICY_REL_PATH ".magisk/selinux/load"
#define MAGISK_POLICY_MAX_SIZE (8 * 1024 * 1024)
#define SELINUX_STATUS_SIZE 20
#define SELINUX_STATUS_CLEAN_SEQUENCE 4
#define SELINUX_STATUS_CLEAN_POLICYLOAD 1
#define KP_AVD_CLEAN_SEQNO 1
#define VM_WRITE 0x00000002
#define VM_MAYWRITE 0x00000020
#define selinux_hook_dbg(fmt, ...) pr_info(fmt, ##__VA_ARGS__)

typedef enum {
    SEL_HOOK_STATE_NORMAL = 0,
    SEL_HOOK_STATE_POLICYDB_REQ,
    SEL_HOOK_STATE_UNSUPORRT
} sel_hook_state_t;

static void *g_funcs[24];
static void *g_hook_befores[24];
static void *g_hook_afters[24];
static int g_hooks;
static long (*copy_from_kernel_nofault_fn)(void *dst, const void *src, size_t size);
static int (*security_load_policy_fn)(void *data, size_t len, struct selinux_load_state *load_state);
static int (*security_context_to_sid_fn)(const char *scontext, u32 scontext_len, u32 *out_sid, gfp_t gfp);
static int (*security_context_to_sid_compat_fn)(void *state, const char *scontext, u32 scontext_len,
                                                u32 *out_sid, gfp_t gfp);
struct policydb;
struct policy_file {
    char *data;
    size_t len;
};

static int (*policydb_read_fn)(struct policydb *policydb, struct policy_file *fp);
static void (*policydb_destroy_fn)(struct policydb *policydb);
static void *(*vmalloc_fn)(unsigned long size);
static void *(*vmalloc_user_fn)(unsigned long size);
static void (*vfree_fn)(const void *addr);
typedef ssize_t (*sel_status_read_fn_t)(struct file *, char __user *, size_t, loff_t *);
typedef int (*sel_status_mmap_fn_t)(struct file *, struct vm_area_struct *);
static sel_status_read_fn_t sel_read_status_fp_orig_fn;
static sel_status_mmap_fn_t sel_mmap_status_fp_orig_fn;
static int (*remap_vmalloc_range_fn)(struct vm_area_struct *, void *, unsigned long);
static struct file *(*filp_open_fn)(const char *filename, int flags, umode_t mode);
static int (*filp_close_fn)(struct file *filp, fl_owner_t id);
static ssize_t (*kernel_read_fn)(struct file *file, void *buf, size_t count, loff_t *pos);
static loff_t (*vfs_llseek_fn)(struct file *file, loff_t offset, int whence);
static void *g_selinux_state;

static bool g_selinux_ready;
static bool g_dirty_policy_seen;
static void *g_first_policydb;
static u32 g_clean_access_count;
static void *g_clean_policy_blob;
static size_t g_clean_policy_len;
static bool g_clean_policy_has_magisk;
static bool g_clean_policydb_direct;
static void *g_clean_policydb;
static bool g_policy_capture_in_progress;
static size_t g_page_size;

struct access_probe {
    u32 id;
    uid_t uid;
    const char *node;
    char query[ACCESS_SAMPLE_MAX];
};

struct clean_eval_scope {
    void *task;
    u32 depth;
};

static struct access_probe g_probes[ACCESS_PROBE_SLOTS];
static struct clean_eval_scope g_clean_eval_scope = { NULL, 0 };
static unsigned char g_clean_status_bytes[SELINUX_STATUS_SIZE];
static void *g_status_mmap_page;
static uintptr_t g_status_fp_slots[2];
static void *g_status_fp_orig[2];
static int g_status_fp_hooks;

static bool contains_magisk(const char *s, size_t len);
static bool contains_case_lit(const char *s, size_t len, const char *lit, size_t lit_len);
static bool should_bypass_clean_filter(uid_t uid);
static const char *current_comm(void);
static bool use_legacy_clean_blob_query(void);
static bool clean_policydb_redirect_supported(void);
static bool selinux_state_arg_required(void);
static bool selinux_compat_call_needed(void);
static void zero_bytes(void *dst, size_t len);
static bool snapshot_magisk_policy_file(const char *reason, bool try_relative);
static bool finish_deferred_policy_capture(hook_fargs4_t *a, const char *stage, bool allow_fallback);
static void before_security_load_policy(hook_fargs4_t *a, void *u);
static void after_security_load_policy(hook_fargs4_t *a, void *u);
static void try_load_clean_policydb_from_blob(const char *reason);
static bool enter_clean_eval_scope(void);
static void leave_clean_eval_scope(void);
static bool current_in_clean_eval_scope(void);
static int install_write_op_hooks(void);
static void record_inline_hook(void *func, void *before, void *after);
static void uninstall_inline_hooks(void);
static void uninstall_status_fp_hooks(void);
static void uninstall_all_hooks(void);
static bool install_status_hooks(void);

/*
 * Patch the seqno field (5th whitespace-separated token, formatted as "%u")
 * in a /sys/fs/selinux/access response buffer to new_seqno.
 * Format: "%x %x %x %x %u %x"
 * Returns the new length (may differ if decimal widths differ).
 */
static ssize_t patch_response_seqno(char *buf, ssize_t ret, u32 new_seqno)
{
    char *p = buf;
    char *end = buf + ret;
    char *tok_start;
    char new_str[12];
    int ns_len;
    int tok;
    ssize_t diff;

    if (ret <= 0 || !buf)
        return ret;

    /* Skip 4 space-separated tokens to reach the 5th (seqno) */
    for (tok = 0; tok < 4; tok++) {
        while (p < end && *p == ' ') p++;
        while (p < end && *p != ' ') p++;
    }
    while (p < end && *p == ' ') p++;
    tok_start = p;
    while (p < end && *p != ' ' && *p != '\0' && *p != '\n') p++;

    if (tok_start >= p)
        return ret;

    /* Render new_seqno as decimal */
    {
        u32 v = new_seqno;
        int i = 0;
        char tmp[12];
        if (v == 0) {
            new_str[0] = '0';
            ns_len = 1;
        } else {
            while (v > 0) { tmp[i++] = '0' + (v % 10); v /= 10; }
            for (ns_len = 0; ns_len < i; ns_len++)
                new_str[ns_len] = tmp[i - 1 - ns_len];
        }
    }

    diff = (ssize_t)ns_len - (ssize_t)(p - tok_start);
    if (diff != 0) {
        /* Shift the remainder of the string left or right */
        char *dst = tok_start + ns_len;
        char *src = p;
        size_t move = (size_t)(end - src);
        int j;
        if (diff < 0) {
            for (j = 0; j < (int)move; j++) dst[j] = src[j];
        } else {
            for (j = (int)move - 1; j >= 0; j--) dst[j] = src[j];
        }
        ret += diff;
    }

    {
        int k;
        for (k = 0; k < ns_len; k++)
            tok_start[k] = new_str[k];
    }
    return ret;
}

static void copy_bytes(void *dst, const void *src, size_t len)
{
    size_t i;
    volatile char *d = (volatile char *)dst;
    const volatile char *s = (const volatile char *)src;

    if (!d || !s)
        return;

    for (i = 0; i < len; i++)
        d[i] = s[i];
}

static void zero_bytes(void *dst, size_t len)
{
    size_t i;
    volatile char *d = (volatile char *)dst;

    if (!d)
        return;

    for (i = 0; i < len; i++)
        d[i] = 0;
}

static size_t runtime_page_size(void)
{
    uint64_t tcr_el1;
    uint64_t tg1;

    /* Match KernelPatch's runtime page-size detection for the TTBR1 range. */
    asm volatile("mrs %0, tcr_el1" : "=r"(tcr_el1));
    tg1 = (tcr_el1 >> 30) & 0x3;

    if (tg1 == 1)
        return 16 * 1024;
    if (tg1 == 3)
        return 64 * 1024;
    return 4 * 1024;
}

static void put_u32_le(unsigned char *dst, u32 value)
{
    if (!dst)
        return;

    dst[0] = (unsigned char)(value & 0xff);
    dst[1] = (unsigned char)((value >> 8) & 0xff);
    dst[2] = (unsigned char)((value >> 16) & 0xff);
    dst[3] = (unsigned char)((value >> 24) & 0xff);
}

static u32 get_u32_le(const unsigned char *src)
{
    if (!src)
        return 0;

    return (u32)src[0] |
           ((u32)src[1] << 8) |
           ((u32)src[2] << 16) |
           ((u32)src[3] << 24);
}

static void fill_clean_status_bytes(unsigned char *status)
{
    u32 seq, pload;

    if (!status)
        return;

    /* kernel >= 6.6: detection expects sequence=4 policyload=1
     * kernel <  6.6: detection expects sequence=0 policyload=0
     * (Java isNewKernel() uses >= 6.10 as threshold, we use 6.6 to
     *  be safe and avoid false positives on kernels in between)
     */
    if (kver >= VERSION(6, 7, 0)) {
        seq   = SELINUX_STATUS_CLEAN_SEQUENCE;
        pload = SELINUX_STATUS_CLEAN_POLICYLOAD;
    } else {
        seq   = 0;
        pload = 0;
    }

    zero_bytes(status, SELINUX_STATUS_SIZE);
    put_u32_le(status + 0,  1);
    put_u32_le(status + 4,  seq);
    put_u32_le(status + 8,  1);    /* enforcing — always 1 */
    put_u32_le(status + 12, pload);
    put_u32_le(status + 16, 1);
}

static bool buffer_contains_magisk(const char *buf, size_t len)
{
    return contains_magisk(buf, len);
}

static bool ascii_lower_eq(char a, char b)
{
    if (a >= 'A' && a <= 'Z')
        a = a - 'A' + 'a';
    if (b >= 'A' && b <= 'Z')
        b = b - 'A' + 'a';
    return a == b;
}

static bool str_eq_lit(const char *s, const char *lit)
{
    size_t i;

    if (!s || !lit)
        return false;

    for (i = 0; lit[i]; i++) {
        if (s[i] != lit[i])
            return false;
    }

    return s[i] == '\0';
}

static const char *current_comm(void)
{
    if (task_struct_offset.comm_offset <= 0)
        return "?";

    return get_task_comm(current) ?: "?";
}

static bool should_bypass_clean_filter(uid_t uid)
{
    if (uid < 10000)
        return true;

    return false;
}

static bool use_legacy_clean_blob_query(void)
{
    return kver < SELINUX_LEGACY_BLOB_QUERY_MAX;
}

static bool clean_policydb_redirect_supported(void)
{
    /*
     * 4.14 reference basis:
     *   - https://github.com/balgxmr/kernel_xiaomi_cepheus/tree/sixteen
     *   - https://github.com/LineageOS/android_kernel_xiaomi_sm8150/tree/lineage-22.2
     *   - https://android.googlesource.com/kernel/common/+/refs/heads/deprecated/android-4.14-stable
     *
     * Relevant source paths:
     *   - security/selinux/ss/services.c
     *       context_struct_compute_av(struct policydb *policydb, ...)
     *       security_context_to_sid(struct selinux_state *state, ...)
     *       security_load_policy(struct selinux_state *state, ...)
     *   - security/selinux/selinuxfs.c
     *       sel_write_access(), sel_write_context()
     *
     * 这里的 4.14 适配不是单纯按 kver 猜 ABI，而是用上述 cepheus/sm8150
      * 4.14 源码确认 SELinux helper 的真实签名。只要运行时能解析到
      * selinux_state，就认为它符合这组 4.14 stateful SELinux 布局；否则
      * policydb redirect 保持关闭，避免把参数强套到未知布局上。
     *
     * The Xiaomi sm8150/cepheus 4.14 lineage keeps selinux_state and also uses
     * the policydb-argument context_struct_compute_av() signature.  Therefore
     * selinux_state is the runtime confidence signal for using the 4.14
     * stateful SELinux helper signatures and the 6-argument policydb redirect
      * path. Kernels older than this baseline do not install policydb hooks.
     */
    return !use_legacy_clean_blob_query() || g_selinux_state;
}

static bool selinux_compat_call_needed(void)
{
    /*
     * 4.14 参考源码里的 security_context_to_sid() 需要
     * struct selinux_state * 作为第一个参数。这里用 selinux_state
     * 作为运行时信号，避免在没有 stateful ABI 的旧内核上误传参数。
     *
     * security_context_to_sid() is stateful on the 4.14 sources listed above.
     * Keep the state argument through the Android common stateful era, and stop
     * before the newer 6.4+ LSM refactors where this KPM has not been audited.
     */
	return g_selinux_state && selinux_state_arg_required();
}

static bool selinux_state_arg_required(void)
{
    return kver >= VERSION(4, 14, 0) && kver < VERSION(6, 4, 0);
}

static size_t str_len_safe(const char *s)
{
    const volatile char *p;
    size_t len = 0;

    if (!s)
        return 0;

    /* Keep this as an explicit byte walk so clang/gcc does not fold it into an
     * out-of-line strlen() libcall, which is unavailable in the KPM loader. */
    p = (const volatile char *)s;
    while (p[len])
        len++;
    return len;
}

static ssize_t call_kernel_read_file(struct file *file, void *buf, size_t count, loff_t *pos)
{
    if (!kernel_read_fn)
        return -ENOENT;

    if (kver < VERSION(4, 14, 0)) {
        loff_t offset = pos ? *pos : 0;
        int (*kernel_read_legacy)(struct file *file, loff_t offset, char *addr,
                                  unsigned long count) =
            (void *)kernel_read_fn;
        int rc = kernel_read_legacy(file, offset, (char *)buf,
                                    (unsigned long)count);

        if (pos && rc > 0)
            *pos = offset + rc;
        return rc;
    }

    return kernel_read_fn(file, buf, count, pos);
}

static bool snapshot_policy_file_path(const char *path, const char *source,
                                      const char *reason)
{
    struct file *filp;
    void *data;
    loff_t len;
    loff_t pos;
    ssize_t nread;

    if (!vmalloc_fn)
        return false;
    if (!filp_open_fn || !filp_close_fn || !kernel_read_fn || !vfs_llseek_fn) {
        pr_warn("[selinux_hook] CLEAN Magisk policy file read disabled reason=%s open=%px close=%px read=%px llseek=%px\n",
                reason ?: "(null)", filp_open_fn, filp_close_fn,
                kernel_read_fn, vfs_llseek_fn);
        return false;
    }

    filp = filp_open_fn(path, O_RDONLY, 0);
    if (!filp || IS_ERR(filp)) {
        pr_warn("[selinux_hook] CLEAN Magisk policy open failed reason=%s source=%s path=%s rc=%ld\n",
                reason ?: "(null)", source ?: "unknown", path,
                filp ? PTR_ERR(filp) : -ENOENT);
        return false;
    }

    len = vfs_llseek_fn(filp, 0, SEEK_END);
    if (len <= 0 || len > MAGISK_POLICY_MAX_SIZE) {
        pr_warn("[selinux_hook] CLEAN Magisk policy bad len reason=%s source=%s path=%s len=%lld\n",
                reason ?: "(null)", source ?: "unknown", path, len);
        filp_close_fn(filp, 0);
        return false;
    }
    vfs_llseek_fn(filp, 0, SEEK_SET);

    data = vmalloc_fn((unsigned long)len);
    if (!data) {
        pr_warn("[selinux_hook] CLEAN Magisk policy alloc failed reason=%s source=%s len=%lld\n",
                reason ?: "(null)", source ?: "unknown", len);
        filp_close_fn(filp, 0);
        return false;
    }

    pos = 0;
    nread = call_kernel_read_file(filp, data, (size_t)len, &pos);
    filp_close_fn(filp, 0);
    if (nread != len || pos != len) {
        pr_warn("[selinux_hook] CLEAN Magisk policy read failed reason=%s source=%s read=%ld pos=%lld len=%lld\n",
                reason ?: "(null)", source ?: "unknown", (long)nread, pos, len);
        if (vfree_fn)
            vfree_fn(data);
        return false;
    }

    WRITE_ONCE(g_clean_policy_has_magisk, buffer_contains_magisk(data, (size_t)len));
    WRITE_ONCE(g_clean_policy_len, (size_t)len);
    WRITE_ONCE(g_clean_policy_blob, data);
    pr_info("[selinux_hook] CLEAN Magisk policy snapshot saved reason=%s source=%s path=%s blob=%px len=%zu has_magisk=%d\n",
            reason ?: "(null)", source ?: "unknown", path, data,
            READ_ONCE(g_clean_policy_len), READ_ONCE(g_clean_policy_has_magisk));
    return true;
}

static bool snapshot_magisk_policy_file(const char *reason, bool try_relative)
{
    if (snapshot_policy_file_path(MAGISK_POLICY_PATH, "magisk_file_abs", reason))
        return true;
    if (try_relative &&
        snapshot_policy_file_path(MAGISK_POLICY_REL_PATH, "magisk_file_rel", reason))
        return true;
    return false;
}

static void try_load_clean_policydb_from_blob(const char *reason)
{
    struct policy_file fp;
    struct policydb *policydb;
    void *blob = READ_ONCE(g_clean_policy_blob);
    size_t len = READ_ONCE(g_clean_policy_len);
    int rc;

    if (READ_ONCE(g_clean_policydb))
        return;
    if (!blob || !len)
        return;
    if (!policydb_read_fn || !policydb_destroy_fn || !vmalloc_fn)
        return;

    policydb = (struct policydb *)vmalloc_fn(CLEAN_POLICYDB_ALLOC_SIZE);
    if (!policydb) {
        pr_warn("[selinux_hook] CLEAN policydb_read alloc failed reason=%s size=%u\n",
                reason ?: "(null)", CLEAN_POLICYDB_ALLOC_SIZE);
        return;
    }
    zero_bytes(policydb, CLEAN_POLICYDB_ALLOC_SIZE);

    fp.data = (char *)blob;
    fp.len = len;
    rc = policydb_read_fn(policydb, &fp);
    if (rc) {
        pr_warn("[selinux_hook] CLEAN policydb_read failed reason=%s rc=%d policydb=%px blob=%px len=%zu\n",
                reason ?: "(null)", rc, policydb, blob, len);
        if (policydb_destroy_fn)
            policydb_destroy_fn(policydb);
        if (vfree_fn)
            vfree_fn(policydb);
        return;
    }

    WRITE_ONCE(g_clean_policydb, policydb);
    WRITE_ONCE(g_clean_policydb_direct, true);
    pr_info("[selinux_hook] CLEAN policydb_read saved reason=%s policydb=%px blob=%px len=%zu alloc=%u\n",
            reason ?: "(null)", policydb, blob, len, CLEAN_POLICYDB_ALLOC_SIZE);
}

static void activate_clean_policy_blob(const char *reason)
{
    if (READ_ONCE(g_clean_policy_blob) && READ_ONCE(g_clean_policy_len))
        try_load_clean_policydb_from_blob(reason);
}

static void snapshot_clean_policy(const char *reason)
{
    if (READ_ONCE(g_clean_policy_blob))
        return;
    if (READ_ONCE(g_dirty_policy_seen))
        return;

    if (!snapshot_magisk_policy_file(reason, true))
        return;

    activate_clean_policy_blob(reason);
}

static bool finish_deferred_policy_capture(hook_fargs4_t *a, const char *stage,
                                           bool allow_fallback)
{
    void *data = NULL;
    size_t len = 0;

    if (READ_ONCE(g_clean_policy_blob))
        return true;
    if (READ_ONCE(g_dirty_policy_seen))
        return false;

    if (snapshot_magisk_policy_file(stage, true)) {
        activate_clean_policy_blob(stage);
        return READ_ONCE(g_clean_policy_blob) != NULL;
    }

    if (!allow_fallback) {
        selinux_hook_dbg("[selinux_hook] CLEAN Magisk policy unavailable during %s; waiting for after security_load_policy\n",
                         stage ?: "before");
        return false;
    }

    if (!a)
        return false;

    if (selinux_compat_call_needed()) {
        data = (void *)a->arg1;
        len = (size_t)a->arg2;
    } else {
        data = (void *)a->arg0;
        len = (size_t)a->arg1;
    }

    if (!data || !len || len > MAGISK_POLICY_MAX_SIZE || !vmalloc_fn) {
        pr_warn("[selinux_hook] CLEAN security_load_policy fallback rejected stage=%s data=%px len=%zu vmalloc=%px\n",
                stage ?: "after", data, len, vmalloc_fn);
        return false;
    }

    {
        void *src = data;
        void *copy = vmalloc_fn((unsigned long)len);

        if (!copy) {
            pr_warn("[selinux_hook] CLEAN security_load_policy fallback alloc failed stage=%s len=%zu\n",
                    stage ?: "after", len);
            return false;
        }
        copy_bytes(copy, src, len);
        data = copy;
    }
    if (!data) {
        pr_warn("[selinux_hook] CLEAN security_load_policy fallback alloc failed stage=%s len=%zu\n",
                stage ?: "after", len);
        return false;
    }

    WRITE_ONCE(g_clean_policy_has_magisk, buffer_contains_magisk(data, len));
    WRITE_ONCE(g_clean_policy_len, len);
    WRITE_ONCE(g_clean_policy_blob, data);
    pr_warn("[selinux_hook] CLEAN policy captured from security_load_policy args stage=%s blob=%px len=%zu has_magisk=%d\n",
            stage ?: "after", data, len, READ_ONCE(g_clean_policy_has_magisk));
    activate_clean_policy_blob(stage ?: "security_load_policy");
    return true;
}

static void before_security_load_policy(hook_fargs4_t *a, void *u)
{
    if (READ_ONCE(g_clean_policy_blob) || g_policy_capture_in_progress)
        return;

    g_policy_capture_in_progress = true;
    finish_deferred_policy_capture(a, "before_security_load_policy", false);
    g_policy_capture_in_progress = false;
}

static void after_security_load_policy(hook_fargs4_t *a, void *u)
{
    if (READ_ONCE(g_clean_policy_blob) || g_policy_capture_in_progress)
        return;
    if (a && (long)a->ret)
        return;

    g_policy_capture_in_progress = true;
    finish_deferred_policy_capture(a, "after_security_load_policy", true);
    g_policy_capture_in_progress = false;
}

static bool contains_magisk(const char *s, size_t len)
{
    return contains_case_literal(s, len, "magisk");
}

static bool contains_case_lit(const char *s, size_t len, const char *lit, size_t lit_len)
{
    size_t i;
    size_t j;

    if (!s || !lit || !lit_len || len < lit_len)
        return false;

    for (i = 0; i + lit_len <= len; i++) {
        for (j = 0; j < lit_len; j++) {
            if (!ascii_lower_eq(s[i + j], lit[j]))
                break;
        }
        if (j == lit_len)
            return true;
    }

    return false;
}

static size_t sanitize_query_sample(char *dst, size_t size)
{
    size_t i;

    if (!dst)
        return 0;

    for (i = 0; i < size && i < ACCESS_SAMPLE_MAX - 1; i++) {
        char c = dst[i];

        if (!c)
            break;
        if (c == '\n' || c == '\r' || c == '\t')
            c = ' ';
        dst[i] = c;
    }

    dst[i] = '\0';
    return i;
}

static size_t copy_query_sample(char *dst, const char *src, size_t size)
{
    size_t limit;
    long copied;

    if (!dst || !src)
        return 0;

    limit = size;
    if (!limit || limit > ACCESS_SAMPLE_MAX - 1)
        limit = ACCESS_SAMPLE_MAX - 1;

    dst[0] = '\0';

    if (copy_from_kernel_nofault_fn &&
        copy_from_kernel_nofault_fn(dst, src, limit) == 0) {
        dst[limit] = '\0';
        return sanitize_query_sample(dst, limit);
    }

    copied = compat_strncpy_from_user(dst, (const char __user *)src, limit + 1);
    if (copied <= 0) {
        dst[0] = '\0';
        return 0;
    }

    if ((size_t)copied > limit)
        copied = limit;
    return sanitize_query_sample(dst, (size_t)copied);
}

static bool enter_clean_eval_scope(void) {
    void *task = current;

    if (!clean_policydb_redirect_supported())
        return false;
    if (!READ_ONCE(g_clean_policydb))
        return false;

    /*
     * Task-keyed and synchronous: only the task that entered the scope is
     * redirected.  The slot is advisory -- if another task holds it we just
     * fall back to the live policy, so no atomicity is required.
     */
    if (g_clean_eval_scope.task == task) {
        g_clean_eval_scope.depth++;
    } else if (!g_clean_eval_scope.task) {
        g_clean_eval_scope.task = task;
        g_clean_eval_scope.depth = 1;
    } else {
        return false;
    }
    return true;
}
 
static void leave_clean_eval_scope(void) {
    void *task = current;
    if (g_clean_eval_scope.task == task) {
        if (g_clean_eval_scope.depth > 1) {
            g_clean_eval_scope.depth--;
        } else {
            g_clean_eval_scope.depth = 0;
            g_clean_eval_scope.task = NULL;
        }
    }
}

static bool current_in_clean_eval_scope(void) {
    void *task = current;
    return g_clean_eval_scope.task == task && g_clean_eval_scope.depth;
}

/* Hook: selinux_complete_init */
static void after_selinux_complete_init(hook_fargs0_t *a, void *u)
{
    WRITE_ONCE(g_selinux_ready, true);
    selinux_hook_dbg("[selinux_hook] SELinux complete_init done\n");
    snapshot_clean_policy("complete_init");
}

/* Hook: selinux_policy_commit */
static void after_selinux_policy_commit(hook_fargs2_t *a, void *u)
{
    WRITE_ONCE(g_selinux_ready, true);
    selinux_hook_dbg("[selinux_hook] SELinux policy committed, first policydb=%px clean policydb=%px\n",
                     g_first_policydb, READ_ONCE(g_clean_policydb));
    snapshot_clean_policy("policy_commit");
}

static void before_policydb_arg0(hook_fargs6_t *a, void *u)
{
    void *policydb = (void *)a->arg0;
    void *clean_policydb = READ_ONCE(g_clean_policydb);
    bool bypass = should_bypass_clean_filter(current_uid());

    if (!clean_policydb_redirect_supported())
        return;

    if (bypass)
        return;
    
    
    /*
     * Only calls running in an explicit clean-eval scope may redirect policydb
     * input.  The scope is tied to current so unrelated callers on other tasks
     * remain observational and keep using the live policydb.
     */
    if (current_in_clean_eval_scope() && clean_policydb) {
        a->arg0 = (uint64_t)clean_policydb;
        return;
    }

    if (!policydb)
        return;

    if (!READ_ONCE(g_selinux_ready)) {
        WRITE_ONCE(g_selinux_ready, true);
        selinux_hook_dbg("[selinux_hook] SELinux ready inferred from context_struct_compute_av\n");
    }

    if (!READ_ONCE(g_first_policydb)) {
        WRITE_ONCE(g_first_policydb, policydb);
        selinux_hook_dbg("[selinux_hook] SAVED first policydb @ %px\n", g_first_policydb);
        snapshot_clean_policy("first_compute_av");
        return;
    }

    if (!READ_ONCE(g_dirty_policy_seen) &&
        policydb != READ_ONCE(g_first_policydb) &&
        policydb != READ_ONCE(g_clean_policydb)) {
        WRITE_ONCE(g_dirty_policy_seen, true);
        selinux_hook_dbg("[selinux_hook] policydb changed %px -> %px, Magisk access probes will hit clean-policy EINVAL\n",
                         g_first_policydb, policydb);
    }
}

/* Hook: /sys/fs/selinux/access write handler */
static void before_sel_write_access(hook_fargs4_t *a, void *u)
{
    // if (current_uid() < 10000 || current_is_policy_manager()) {
    //     return; 
    // }
    // pr_info("[selinux_hook] before_sel_write_access called uid=%u\n", current_uid());
    const char *query = (const char *)a->arg1;
    size_t size = (size_t)a->arg2;
    char sample[ACCESS_SAMPLE_MAX];
    u32 slot;
    u32 n;
    uid_t uid;

    a->local.data0 = 0;

    uid = current_uid();

    if (should_bypass_clean_filter(uid))
        return;

    copy_query_sample(sample, query, size);
    n = READ_ONCE(g_clean_access_count) + 1;
    WRITE_ONCE(g_clean_access_count, n);

    /* Run the original selinuxfs write handler under the current task's clean scope. */
    a->local.data0 = 3;
    a->local.data1 = n;
    slot = n & (ACCESS_PROBE_SLOTS - 1);
    a->local.data2 = slot;
    g_probes[slot].id = n;
    g_probes[slot].uid = uid;
    g_probes[slot].node = "access";
    copy_bytes(g_probes[slot].query, sample, ACCESS_SAMPLE_MAX);
    if (enter_clean_eval_scope()) {
        a->local.data3 = 1;
    } else {
        a->local.data0 = 0;
    }
}

/* Hook: /sys/fs/selinux/context write handler */
static void before_sel_write_context(hook_fargs4_t *a, void *u)
{
    const char *query = (const char *)a->arg1;
    size_t size = (size_t)a->arg2;
    char sample[ACCESS_SAMPLE_MAX];
    u32 slot;
    u32 n;
    uid_t uid;

    a->local.data0 = 0;

    uid = current_uid();

    if (should_bypass_clean_filter(uid))
        return;

    copy_query_sample(sample, query, size);
    n = READ_ONCE(g_clean_access_count) + 1;
    WRITE_ONCE(g_clean_access_count, n);

    a->local.data1 = n;
    slot = n & (ACCESS_PROBE_SLOTS - 1);
    a->local.data2 = slot;
    g_probes[slot].id = n;
    g_probes[slot].uid = uid;
    g_probes[slot].node = "context";
    copy_bytes(g_probes[slot].query, sample, ACCESS_SAMPLE_MAX);

    a->local.data0 = 3;
    if (enter_clean_eval_scope()) {
        a->local.data3 = 1;
    } else {
        a->local.data0 = 0;
    }
}

static void after_sel_write_common(hook_fargs4_t *a, void *u)
{
    long live_ret;
    struct access_probe *probe;
    u32 id;
    u32 slot;

    if (!a->local.data0)
        return;

    id = (u32)a->local.data1;
    slot = (u32)a->local.data2;
    if (a->local.data3)
        leave_clean_eval_scope();

    probe = &g_probes[slot];
    if (probe->id != id)
        return;

    live_ret = (long)a->ret;

    /* Patch seqno in the access response buffer to match /sys/fs/selinux/status */
    if (live_ret > 0 && probe->node && probe->node[0] == 'a') {
        char *rbuf = (char *)a->arg1;
        ssize_t new_ret = patch_response_seqno(rbuf, live_ret, KP_AVD_CLEAN_SEQNO);
        if (new_ret > 0) {
            live_ret = new_ret;
            a->ret = (uint64_t)new_ret;
        }
    }

    selinux_hook_dbg("[selinux_hook] CLEAN /sys/fs/selinux/%s #%u uid=%d comm=%s clean_ret=%ld clean_policydb=%px blob=%px len=%zu query=\"%s\"\n",
                         probe->node ?: "?", id, probe->uid, current_comm(), live_ret,
                         READ_ONCE(g_clean_policydb), READ_ONCE(g_clean_policy_blob),
                         READ_ONCE(g_clean_policy_len), probe->query);
}

static int install_write_op_hooks(void)
{
    unsigned long addr_access, addr_context;
    hook_err_t hook_err;

    if (!clean_policydb_redirect_supported())
        return -EOPNOTSUPP;

    /* Direct symbols are required; no pointer-table fallback is available. */
    addr_access = (unsigned long)kallsyms_lookup_name_by_suffix("sel_write_access");
    addr_context = (unsigned long)kallsyms_lookup_name_by_suffix("sel_write_context");

    if (!addr_access) {
        pr_warn("[selinux_hook] sel_write_access unresolved; direct access/context hooks unavailable\n");
        return -EOPNOTSUPP;
    }

    if (g_hooks + (addr_context ? 2 : 1) >
        (int)(sizeof(g_funcs) / sizeof(g_funcs[0])))
        return -ENOSPC;

    pr_info("[selinux_hook] hook sel_write_access argc=3 mode=direct\n");
    hook_err = hook_wrap((void *)addr_access, 3, before_sel_write_access,
                         after_sel_write_common, NULL);
    if (hook_err != HOOK_NO_ERR) {
        pr_err("[selinux_hook] hook sel_write_access failed err=%d\n",
               (int)hook_err);
        return (int)hook_err;
    }
    record_inline_hook((void *)addr_access, before_sel_write_access,
                       after_sel_write_common);
    selinux_hook_dbg("[selinux_hook] inline hook sel_write_access @ %lx\n", addr_access);

    if (addr_context) {
        pr_info("[selinux_hook] hook sel_write_context argc=3 mode=direct\n");
        hook_err = hook_wrap((void *)addr_context, 3,
                             before_sel_write_context,
                             after_sel_write_common, NULL);
        if (hook_err != HOOK_NO_ERR) {
            pr_err("[selinux_hook] hook sel_write_context failed err=%d\n",
                   (int)hook_err);
            hook_unwrap((void *)addr_access, before_sel_write_access,
                        after_sel_write_common);
            g_hooks--;
            g_funcs[g_hooks] = NULL;
            g_hook_befores[g_hooks] = NULL;
            g_hook_afters[g_hooks] = NULL;
            return (int)hook_err;
        }
        record_inline_hook((void *)addr_context, before_sel_write_context,
                           after_sel_write_common);
        selinux_hook_dbg("[selinux_hook] inline hook sel_write_context @ %lx\n", addr_context);
    } else {
        pr_warn("[selinux_hook] sel_write_context not found, context hook skipped\n");
    }
    return 0;
}

static void record_inline_hook(void *func, void *before, void *after)
{
    g_funcs[g_hooks] = func;
    g_hook_befores[g_hooks] = before;
    g_hook_afters[g_hooks] = after;
    g_hooks++;
}

static void uninstall_inline_hooks(void)
{
    int i;

    for (i = 0; i < g_hooks; i++)
        hook_unwrap(g_funcs[i], g_hook_befores[i], g_hook_afters[i]);
    g_hooks = 0;
}

static bool install_status_fp_hook(uintptr_t slot, void *replace,
                                   void **backup, const char *name)
{
    if (!slot || !replace || !backup)
        return false;

    if (g_status_fp_hooks >= (int)(sizeof(g_status_fp_slots) /
                                   sizeof(g_status_fp_slots[0]))) {
        pr_warn("[selinux_hook] status fp hook table full for %s\n", name);
        return false;
    }

    *backup = NULL;
    fp_hook(slot, replace, backup);
    if (!*backup) {
        pr_warn("[selinux_hook] status fp hook failed for %s slot=%px\n",
                name, (void *)slot);
        return false;
    }

    g_status_fp_slots[g_status_fp_hooks] = slot;
    g_status_fp_orig[g_status_fp_hooks] = *backup;
    g_status_fp_hooks++;
    pr_info("[selinux_hook] status fp hook installed for %s slot=%px\n",
            name, (void *)slot);
    return true;
}

#define STATUS_FOPS_SCAN_ENTRIES 32

static unsigned long read_status_fops_slot(uintptr_t slot)
{
    if (!slot || is_bad_address((void *)slot))
        return 0;
    return READ_ONCE(*(unsigned long *)slot);
}

/* Resolve the fp_hook target by the handler address, not by a file_operations
 * field number.  The layout differs between kernel revisions and vendor
 * trees; fp_hook still receives the address of the matching pointer slot. */
static uintptr_t find_status_fops_slot(unsigned long status_ops,
                                       unsigned long handler)
{
    unsigned long *ops;
    int i;

    if (!status_ops || !handler || is_bad_address((void *)status_ops))
        return 0;

    ops = (unsigned long *)status_ops;
    for (i = 0; i < STATUS_FOPS_SCAN_ENTRIES; i++) {
        uintptr_t slot = (uintptr_t)&ops[i];

        if (is_bad_address((void *)slot))
            break;
        if (read_status_fops_slot(slot) == handler)
            return slot;
    }
    return 0;
}

static void uninstall_status_fp_hooks(void)
{
    int i;

    for (i = g_status_fp_hooks - 1; i >= 0; i--) {
        if (g_status_fp_slots[i])
            fp_unhook(g_status_fp_slots[i], g_status_fp_orig[i]);
        g_status_fp_slots[i] = 0;
        g_status_fp_orig[i] = NULL;
    }
    g_status_fp_hooks = 0;
    sel_read_status_fp_orig_fn = NULL;
    sel_mmap_status_fp_orig_fn = NULL;
}

static void uninstall_all_hooks(void)
{
    uninstall_inline_hooks();
    uninstall_status_fp_hooks();
}

/* Hook: selinux_setprocattr(name, value, size) clean-policy wrapper */
static void before_selinux_setprocattr_clean_eval(hook_fargs3_t *a, void *u)
{
    const char *name = (const char *)a->arg0;
    uid_t uid = current_uid();

    a->local.data0 = 0;

    if (should_bypass_clean_filter(uid) || !str_eq_lit(name, "current"))
        return;

    if (enter_clean_eval_scope())
        a->local.data0 = 1;
}

static void after_selinux_setprocattr_clean_eval(hook_fargs3_t *a, void *u)
{
    if (a->local.data0)
        leave_clean_eval_scope();
}

/* /sys/fs/selinux/status has independent read and mmap handlers. */
static ssize_t read_clean_status_bytes(char __user *buffer, size_t count,
                                       loff_t *ppos)
{
    loff_t pos;
    size_t available;

    if (!ppos || (pos = *ppos) < 0)
        return -EINVAL;
    if (!count || pos >= (loff_t)sizeof(g_clean_status_bytes))
        return 0;

    available = sizeof(g_clean_status_bytes) - (size_t)pos;
    if (count > available)
        count = available;
    if (compat_copy_to_user(buffer, g_clean_status_bytes + (size_t)pos,
                            (int)count) != (int)count)
        return -EFAULT;

    *ppos = pos + (loff_t)count;
    return (ssize_t)count;
}

static int remap_clean_status_page(struct vm_area_struct *vma)
{
    if (kver < VERSION(4, 15, 0)) {
        unsigned long vm_start = *(unsigned long *)((char *)vma + 0);
        unsigned long vm_end = *(unsigned long *)((char *)vma + 8);
        unsigned long vm_flags = *(unsigned long *)((char *)vma + 80);
        unsigned long vm_pgoff = *(unsigned long *)((char *)vma + 152);

        if (vm_pgoff > 0 || (vm_end - vm_start) != g_page_size)
            return -EIO;
        if (vm_flags & VM_WRITE)
            return -EPERM;
        *(unsigned long *)((char *)vma + 80) = vm_flags & ~VM_MAYWRITE;
    }
    return remap_vmalloc_range_fn(vma, g_status_mmap_page, 0);
}

static ssize_t sel_read_handle_status_fp_hook(struct file *file,
                                              char __user *buffer,
                                              size_t count, loff_t *ppos)
{
    if (should_bypass_clean_filter(current_uid())) {
        if (sel_read_status_fp_orig_fn)
            return sel_read_status_fp_orig_fn(file, buffer, count, ppos);
        return -ENOSYS;
    }
    return read_clean_status_bytes(buffer, count, ppos);
}

static int sel_mmap_handle_status_fp_hook(struct file *file,
                                          struct vm_area_struct *vma)
{
    if (should_bypass_clean_filter(current_uid())) {
        if (sel_mmap_status_fp_orig_fn)
            return sel_mmap_status_fp_orig_fn(file, vma);
        return -ENOSYS;
    }

    if (!g_status_mmap_page || !remap_vmalloc_range_fn) {
        if (sel_mmap_status_fp_orig_fn)
            return sel_mmap_status_fp_orig_fn(file, vma);
        return -ENOSYS;
    }

    if (!remap_vmalloc_range_fn(vma, g_status_mmap_page, 0))
        return 0;

    if (sel_mmap_status_fp_orig_fn)
        return sel_mmap_status_fp_orig_fn(file, vma);
    return -ENOSYS;
}

static void before_sel_read_handle_status(hook_fargs4_t *a, void *u)
{
    if (!should_bypass_clean_filter(current_uid())) {
        a->ret = (uint64_t)read_clean_status_bytes(
            (char __user *)a->arg1, (size_t)a->arg2, (loff_t *)a->arg3);
        a->skip_origin = 1;
    }
}

static void before_sel_mmap_handle_status(hook_fargs4_t *a, void *u)
{
    if (should_bypass_clean_filter(current_uid()) || !g_status_mmap_page || !remap_vmalloc_range_fn)
        return;

    a->ret = remap_clean_status_page((struct vm_area_struct *)a->arg1);
    a->skip_origin = 1;
}

static bool install_status_hooks(void)
{
    unsigned long read_addr;
    unsigned long mmap_addr;
    unsigned long status_ops;
    uintptr_t slot;
    hook_err_t err;
    bool installed = false;
    bool read_installed = false;
    bool mmap_installed = false;

    read_addr = (unsigned long)kallsyms_lookup_name_by_suffix("sel_read_handle_status");
    mmap_addr = (unsigned long)kallsyms_lookup_name_by_suffix("sel_mmap_handle_status");
    status_ops = (unsigned long)kallsyms_lookup_name_by_suffix("sel_handle_status_ops");

    if (read_addr) {
        err = hook_wrap((void *)read_addr, 4, before_sel_read_handle_status, NULL, NULL);
        if (err == HOOK_NO_ERR) {
            record_inline_hook((void *)read_addr, before_sel_read_handle_status, NULL);
            pr_info("[selinux_hook] status read inline hook installed @%px\n",
                    (void *)read_addr);
            installed = true;
            read_installed = true;
        }
    }

    if (!read_installed && read_addr && status_ops) {
        slot = find_status_fops_slot(status_ops, read_addr);
        if (install_status_fp_hook(slot, (void *)sel_read_handle_status_fp_hook,
                                   (void **)&sel_read_status_fp_orig_fn,
                                   "sel_read_handle_status")) {
            installed = true;
            read_installed = true;
        }
    }

    if (!read_installed)
        pr_warn("[selinux_hook] status read unavailable handler=%px status_ops=%px\n",
                (void *)read_addr, (void *)status_ops);

    remap_vmalloc_range_fn = (void *)kallsyms_lookup_name_by_suffix("remap_vmalloc_range");
    if (remap_vmalloc_range_fn && vmalloc_user_fn && !g_status_mmap_page) {
        g_status_mmap_page = vmalloc_user_fn(g_page_size);
        if (g_status_mmap_page) {
            zero_bytes(g_status_mmap_page, g_page_size);
            copy_bytes(g_status_mmap_page, g_clean_status_bytes,
                       sizeof(g_clean_status_bytes));
        }
    }

    if (mmap_addr && g_status_mmap_page && remap_vmalloc_range_fn) {
        err = hook_wrap((void *)mmap_addr, 2, before_sel_mmap_handle_status, NULL, NULL);
        if (err == HOOK_NO_ERR) {
            record_inline_hook((void *)mmap_addr, before_sel_mmap_handle_status, NULL);
            pr_info("[selinux_hook] status mmap inline hook installed @%px fake_page=%px size=%zu\n",
                    (void *)mmap_addr, g_status_mmap_page, g_page_size);
            installed = true;
            mmap_installed = true;
        }
    }

    if (!mmap_installed && mmap_addr && status_ops && g_status_mmap_page &&
        remap_vmalloc_range_fn) {
        slot = find_status_fops_slot(status_ops, mmap_addr);
        if (install_status_fp_hook(slot, (void *)sel_mmap_handle_status_fp_hook,
                                   (void **)&sel_mmap_status_fp_orig_fn,
                                   "sel_mmap_handle_status")) {
            installed = true;
            mmap_installed = true;
        }
    }

    if (!mmap_installed)
        pr_warn("[selinux_hook] status mmap unavailable handler=%px status_ops=%px remap=%px vmalloc_user=%px fake_page=%px\n",
                (void *)mmap_addr, (void *)status_ops,
                remap_vmalloc_range_fn, vmalloc_user_fn, g_status_mmap_page);

    return installed;
}

static long init(const char *args, const char *event, void *__user r)
{
    unsigned long addr;
    int rc;

    g_page_size = runtime_page_size();

    selinux_hook_dbg("[selinux_hook] init event=%s\n", event ?: "(null)");

    /* Initialize clean status bytes based on kernel version */
    fill_clean_status_bytes(g_clean_status_bytes);
    selinux_hook_dbg("[selinux_hook] clean status: kver=%u.%u seq=%u pload=%u\n",
                     (unsigned)(kver >> 16), (unsigned)((kver >> 8) & 0xff),
                     get_u32_le(g_clean_status_bytes + 4),
                     get_u32_le(g_clean_status_bytes + 12));
    pr_info("[selinux_hook] kernel kver=%x legacy_blob_abi=%d\n",
            kver, use_legacy_clean_blob_query() ? 1 : 0);

    copy_from_kernel_nofault_fn = (void *)kallsyms_lookup_name_by_suffix("copy_from_kernel_nofault");
    if (!copy_from_kernel_nofault_fn)
        copy_from_kernel_nofault_fn = (void *)kallsyms_lookup_name_by_suffix("probe_kernel_read");
    vmalloc_fn = (void *)kallsyms_lookup_name_by_suffix("vmalloc");
    if (!vmalloc_fn)
        vmalloc_fn = (void *)kallsyms_lookup_name_by_suffix("vmalloc_noprof");
    vmalloc_user_fn = (void *)kallsyms_lookup_name_by_suffix("vmalloc_user");
    vfree_fn = (void *)kallsyms_lookup_name_by_suffix("vfree");
    filp_open_fn = (void *)kallsyms_lookup_name_by_suffix("filp_open");
    filp_close_fn = (void *)kallsyms_lookup_name_by_suffix("filp_close");
    kernel_read_fn = (void *)kallsyms_lookup_name_by_suffix("kernel_read");
    vfs_llseek_fn = (void *)kallsyms_lookup_name_by_suffix("vfs_llseek");
    g_selinux_state = kallsyms_lookup_name_by_suffix("selinux_state");
    if (!filp_open_fn || !filp_close_fn || !kernel_read_fn || !vfs_llseek_fn)
        pr_warn("[selinux_hook] cannot find file-read symbols: filp_open=%px filp_close=%px kernel_read=%px vfs_llseek=%px\n",
                filp_open_fn, filp_close_fn, kernel_read_fn, vfs_llseek_fn);
    security_load_policy_fn = (void *)kallsyms_lookup_name_by_suffix("security_load_policy");
    security_context_to_sid_fn = (void *)kallsyms_lookup_name_by_suffix("security_context_to_sid");
    security_context_to_sid_compat_fn = (void *)security_context_to_sid_fn;
    policydb_read_fn = (void *)kallsyms_lookup_name_by_suffix("policydb_read");
    policydb_destroy_fn = (void *)kallsyms_lookup_name_by_suffix("policydb_destroy");
    pr_info("[selinux_hook] compat route: state_calls=%d policydb_redirect=%d\n",
            selinux_compat_call_needed() ? 1 : 0,
            clean_policydb_redirect_supported() ? 1 : 0);
    if (selinux_compat_call_needed())
        pr_info("[selinux_hook] SELinux compat calls enabled kver=%x state=%px\n",
                kver, g_selinux_state);
    /* Keep the clean policy snapshot available to redirect-capable hooks. */
    snapshot_clean_policy("module_init");
    if (!security_context_to_sid_fn)
        pr_warn("[selinux_hook] cannot find security_context_to_sid, procattr clean-policy redirect unavailable\n");
    if (!policydb_read_fn || !policydb_destroy_fn)
        pr_warn("[selinux_hook] cannot find policydb_read/policydb_destroy, clean policydb redirect disabled\n");
    if (install_status_hooks())
        pr_info("[selinux_hook] status handler hooks installed\n");
    else
        pr_warn("[selinux_hook] no status handler hooks installed; native status paths remain active\n");

    if (!security_load_policy_fn) {
        pr_warn("[selinux_hook] cannot find security_load_policy, deferred clean policy capture disabled\n");
    } else if (!READ_ONCE(g_clean_policy_blob)) {
        int argc = selinux_compat_call_needed() ? 4 : 3;

        record_inline_hook((void *)security_load_policy_fn,
                           before_security_load_policy,
                           after_security_load_policy);
        pr_info("[selinux_hook] hook security_load_policy argc=%d for deferred Magisk policy capture\n", argc);
        hook_wrap((void *)security_load_policy_fn, argc,
                  before_security_load_policy, after_security_load_policy, NULL);
    } else {
        selinux_hook_dbg("[selinux_hook] security_load_policy capture skipped; clean policy already loaded\n");
    }

    if (clean_policydb_redirect_supported()) {
        addr = (unsigned long)kallsyms_lookup_name_by_suffix("selinux_setprocattr");
        if (addr) {
            record_inline_hook((void *)addr, before_selinux_setprocattr_clean_eval,
                               after_selinux_setprocattr_clean_eval);
            selinux_hook_dbg("[selinux_hook] hook selinux_setprocattr argc=3 clean-eval\n");
            hook_wrap((void *)addr, 3, before_selinux_setprocattr_clean_eval,
                      after_selinux_setprocattr_clean_eval, NULL);
        } else {
            pr_warn("[selinux_hook] cannot find selinux_setprocattr\n");
        }
    } else {
        selinux_hook_dbg("[selinux_hook] skip selinux_setprocattr clean-eval; policydb redirect unsupported\n");
    }

    if (clean_policydb_redirect_supported()) {
        rc = install_write_op_hooks();
        if (rc == -EOPNOTSUPP) {
            pr_warn("[selinux_hook] direct selinuxfs write hooks unavailable; continuing without access/context redirect\n");
        } else if (rc) {
            uninstall_all_hooks();
            return rc;
        }
    } else {
        selinux_hook_dbg("[selinux_hook] skip /access and /context hooks; policydb redirect unsupported\n");
    }

    /* Policydb redirect hooks / policydb 重定向 hooks. */
	addr = (unsigned long)kallsyms_lookup_name_by_suffix("context_struct_compute_av");
    if (addr && clean_policydb_redirect_supported()) {
        record_inline_hook((void *)addr, before_policydb_arg0, NULL);
        pr_info("[selinux_hook] hook context_struct_compute_av argc=6\n");
        hook_wrap((void *)addr, 6, before_policydb_arg0, NULL, NULL);
    } else if (!addr) {
        pr_warn("[selinux_hook] cannot find context_struct_compute_av\n");
    } else {
        selinux_hook_dbg("[selinux_hook] skip context_struct_compute_av; policydb redirect unsupported\n");
    }

    addr = (unsigned long)kallsyms_lookup_name_by_suffix("string_to_context_struct");
    if (addr) {
        if (clean_policydb_redirect_supported()) {
            record_inline_hook((void *)addr, before_policydb_arg0, NULL);
            pr_info("[selinux_hook] hook string_to_context_struct argc=5\n");
            hook_wrap((void *)addr, 5, before_policydb_arg0, NULL, NULL);
        }
    } else {
        pr_warn("[selinux_hook] cannot find string_to_context_struct\n");
    }

    addr = (unsigned long)kallsyms_lookup_name_by_suffix("selinux_complete_init");
    if (addr) {
        record_inline_hook((void *)addr, NULL, after_selinux_complete_init);
        pr_info("[selinux_hook] hook selinux_complete_init argc=0\n");
        hook_wrap((void *)addr, 0, NULL, after_selinux_complete_init, NULL);
    } else {
        pr_warn("[selinux_hook] cannot find selinux_complete_init\n");
    }

    addr = (unsigned long)kallsyms_lookup_name_by_suffix("selinux_policy_commit");
    if (addr) {
        int argc = selinux_compat_call_needed() ? 2 : 1;

        record_inline_hook((void *)addr, NULL, after_selinux_policy_commit);
        pr_info("[selinux_hook] hook selinux_policy_commit argc=%d mode=%s\n",
                argc, selinux_compat_call_needed() ? "state+load_state" : "load_state");
        hook_wrap((void *)addr, argc, NULL, after_selinux_policy_commit, NULL);
    } else {
        pr_warn("[selinux_hook] cannot find selinux_policy_commit\n");
    }

    selinux_hook_dbg("[selinux_hook] %d hooks installed\n", g_hooks);
    return 0;
}

static long exit_(void *__user r)
{
    uninstall_all_hooks();

    if (g_status_mmap_page) {
        pr_warn("[selinux_hook] UNSAFE: forcing fake SELinux status page free at exit; stale VMA references may cause UAF or a kernel crash\n");
        if (vfree_fn) {
            vfree_fn(g_status_mmap_page);
            g_status_mmap_page = NULL;
        } else {
            pr_err("[selinux_hook] cannot free fake SELinux status page: vfree is unavailable; vmalloc memory remains allocated\n");
        }
    }

    g_policy_capture_in_progress = false;

    if (READ_ONCE(g_clean_policydb_direct) && g_clean_policydb) {
        if (policydb_destroy_fn)
            policydb_destroy_fn((struct policydb *)g_clean_policydb);
        if (vfree_fn)
            vfree_fn(g_clean_policydb);
        g_clean_policydb = NULL;
        g_clean_policydb_direct = false;
    }

    if (g_clean_policy_blob) {
        if (vfree_fn)
            vfree_fn(g_clean_policy_blob);
        g_clean_policy_blob = NULL;
        g_clean_policy_len = 0;
    }

    selinux_hook_dbg("[selinux_hook] exited\n");
    return 0;
}

static sel_hook_state_t module_get_working_mode(void) // Used to identify the working mode
{
    bool redirect_supported = clean_policydb_redirect_supported();
    bool has_clean_policydb = READ_ONCE(g_clean_policydb) != NULL;

    if (!redirect_supported)
        return SEL_HOOK_STATE_UNSUPORRT;
    if (!has_clean_policydb)
        return SEL_HOOK_STATE_POLICYDB_REQ;
    return SEL_HOOK_STATE_NORMAL;
}

static long control(const char* args, char* __user out_msg, int outlen)
{
    sel_hook_state_t state;
    const char *state_str;
    int copied;
    size_t len;

    if (!args || !out_msg || outlen <= 0)
        return -EINVAL;

    if (str_eq_lit(args, "mode")) {
        state = module_get_working_mode();
        switch (state) {
        case SEL_HOOK_STATE_NORMAL:
            state_str = "NORMAL";
            break;
        case SEL_HOOK_STATE_POLICYDB_REQ:
            state_str = "POLICYDB_REQ";
            break;
        case SEL_HOOK_STATE_UNSUPORRT:
            state_str = "UNSUPORRT";
            break;
        default:
            state_str = "UNKNOWN";
            break;
        }

        len = str_len_safe(state_str);
        if (outlen < len)
            return -EINVAL;
        
        copied = compat_copy_to_user(out_msg, state_str, (int)len);
        if (copied != (int)len)
            return -EFAULT;
        
        return 0;
    }
    
    return -EINVAL;
}

KPM_INIT(init);
KPM_CTL0(control);
KPM_EXIT(exit_);
