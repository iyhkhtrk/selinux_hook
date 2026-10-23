/*
 * Audit and filter SELinux access queries that probe Magisk contexts.
 *
 * Tailored for Xiaomi 4.14 (evergo-r-oss) kernel.
 * Completely autonomous clean evaluation engine without task scopes or locks.
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
KPM_VERSION("v0.0.2");
KPM_LICENSE("GPL v3");
KPM_AUTHOR("Admire, 741afb7");
KPM_DESCRIPTION("Clean policy evaluation for Xiaomi 4.14");

#define CLEAN_POLICYDB_ALLOC_SIZE 0x8000
#define CLEAN_SIDTAB_ALLOC_SIZE   0x4000
#define MAGISK_POLICY_PATH "/.magisk/selinux/load"
#define MAGISK_POLICY_REL_PATH ".magisk/selinux/load"
#define MAGISK_POLICY_MAX_SIZE (8 * 1024 * 1024)

#define SELINUX_STATUS_SIZE 20
#define KP_AVD_CLEAN_SEQNO 1
#define VM_WRITE 0x00000002
#define VM_MAYWRITE 0x00000020

#define contains_case_literal(s, len, lit) contains_case_lit((s), (len), (lit), sizeof(lit) - 1)
#define selinux_hook_dbg(fmt, ...) pr_info(fmt, ##__VA_ARGS__)

typedef enum {
    SEL_HOOK_STATE_NORMAL = 0,
    SEL_HOOK_STATE_POLICYDB_REQ,
    SEL_HOOK_STATE_UNSUPORRT
} sel_hook_state_t;

/* Forward declarations */
struct policydb;
struct sidtab;
struct context;
struct policy_file {
    char *data;
    size_t len;
};

/* Registered inline hooks table */
static void *g_funcs[16];
static void *g_hook_befores[16];
static void *g_hook_afters[16];
static int g_hooks;

/* Memory & file operations */
static void *(*vmalloc_fn)(unsigned long size);
static void *(*vmalloc_user_fn)(unsigned long size);
static void (*vfree_fn)(const void *addr);
static struct file *(*filp_open_fn)(const char *filename, int flags, umode_t mode);
static int (*filp_close_fn)(struct file *filp, fl_owner_t id);
static ssize_t (*kernel_read_fn)(struct file *file, void *buf, size_t count, loff_t *pos);
static loff_t (*vfs_llseek_fn)(struct file *file, loff_t offset, int whence);
static int (*remap_vmalloc_range_fn)(struct vm_area_struct *, void *, unsigned long);

/* SELinux core symbols for 4.14 */
static int (*policydb_read_fn)(struct policydb *policydb, struct policy_file *fp);
static void (*policydb_destroy_fn)(struct policydb *policydb);
static int (*sidtab_init_fn)(struct sidtab *s);
static void (*sidtab_destroy_fn)(struct sidtab *s);
static int (*policydb_load_isids_fn)(struct policydb *p, struct sidtab *s);
static struct context *(*sidtab_search_fn)(struct sidtab *s, u32 sid);
static int (*string_to_context_struct_fn)(struct policydb *pol, struct sidtab *sidtab,
                                         char *scontext, struct context *ctx, u32 def_sid);
static int (*sidtab_context_to_sid_fn)(struct sidtab *s, struct context *context, u32 *sid);
static void (*context_struct_compute_av_fn)(struct policydb *policydb,
                                           struct context *scontext,
                                           struct context *tcontext,
                                           u16 tclass,
                                           struct av_decision *avd,
                                           void *xperms);
static void (*context_destroy_fn)(struct context *c);
static int (*security_load_policy_fn)(void *state, void *data, size_t len);

/* Status file operation hooks */
typedef ssize_t (*sel_status_read_fn_t)(struct file *, char __user *, size_t, loff_t *);
typedef int (*sel_status_mmap_fn_t)(struct file *, struct vm_area_struct *);
static sel_status_read_fn_t sel_read_status_fp_orig_fn;
static sel_status_mmap_fn_t sel_mmap_status_fp_orig_fn;
static uintptr_t g_status_fp_slots[2];
static void *g_status_fp_orig[2];
static int g_status_fp_hooks;
static unsigned char g_clean_status_bytes[SELINUX_STATUS_SIZE];
static void *g_status_mmap_page;

/* Clean Policy state */
static void *g_clean_policy_blob;
static size_t g_clean_policy_len;
static void *g_clean_policydb;
static void *g_clean_sidtab;
static bool g_clean_ready;
static bool g_policy_capture_in_progress;
static void *g_selinux_state;

/* String and memory utilities */
static void copy_bytes(void *dst, const void *src, size_t len)
{
    size_t i;
    volatile char *d = (volatile char *)dst;
    const volatile char *s = (const volatile char *)src;
    if (!d || !s) return;
    for (i = 0; i < len; i++) d[i] = s[i];
}

static void zero_bytes(void *dst, size_t len)
{
    size_t i;
    volatile char *d = (volatile char *)dst;
    if (!d) return;
    for (i = 0; i < len; i++) d[i] = 0;
}

static size_t str_len_safe(const char *s)
{
    const volatile char *p;
    size_t len = 0;
    if (!s) return 0;
    p = (const volatile char *)s;
    while (p[len]) len++;
    return len;
}

static bool ascii_lower_eq(char a, char b)
{
    if (a >= 'A' && a <= 'Z') a = a - 'A' + 'a';
    if (b >= 'A' && b <= 'Z') b = b - 'A' + 'a';
    return a == b;
}

static bool str_eq_lit(const char *s, const char *lit)
{
    size_t i;
    if (!s || !lit) return false;
    for (i = 0; lit[i]; i++) {
        if (s[i] != lit[i]) return false;
    }
    return s[i] == '\0';
}

static bool contains_case_lit(const char *s, size_t len, const char *lit, size_t lit_len)
{
    size_t i, j;
    if (!s || !lit || !lit_len || len < lit_len) return false;
    for (i = 0; i + lit_len <= len; i++) {
        for (j = 0; j < lit_len; j++) {
            if (!ascii_lower_eq(s[i + j], lit[j])) break;
        }
        if (j == lit_len) return true;
    }
    return false;
}

static bool contains_magisk(const char *s, size_t len)
{
    return contains_case_literal(s, len, "magisk");
}

static bool should_bypass_clean_filter(uid_t uid)
{
    return uid < 10000;
}

static void put_u32_le(unsigned char *dst, u32 value)
{
    if (!dst) return;
    dst[0] = (unsigned char)(value & 0xff);
    dst[1] = (unsigned char)((value >> 8) & 0xff);
    dst[2] = (unsigned char)((value >> 16) & 0xff);
    dst[3] = (unsigned char)((value >> 24) & 0xff);
}

static void fill_clean_status_bytes(unsigned char *status)
{
    zero_bytes(status, SELINUX_STATUS_SIZE);
    put_u32_le(status + 0,  1);  /* version */
    put_u32_le(status + 4,  0);  /* 4.14 uses sequence = 0 */
    put_u32_le(status + 8,  1);  /* enforcing = 1 */
    put_u32_le(status + 12, 0);  /* policyload = 0 */
    put_u32_le(status + 16, 1);  /* deny_unknown = 1 */
}

/* Clean Evaluation Engine */
static int clean_context_to_sid(const char *scontext, u32 scontext_len, u32 *out_sid)
{
    struct policydb *policydb = (struct policydb *)READ_ONCE(g_clean_policydb);
    struct sidtab *sidtab = (struct sidtab *)READ_ONCE(g_clean_sidtab);
    char ctx_buf[128] __aligned(8);
    struct context *ctx = (struct context *)ctx_buf;
    char stackbuf[256];
    int rc;

    if (!policydb || !sidtab || !scontext || !scontext_len || !out_sid)
        return -EINVAL;
    if (!string_to_context_struct_fn || !sidtab_context_to_sid_fn)
        return -ENOSYS;

    /* Trim length and trailing whitespace/newlines */
    if (scontext_len >= sizeof(stackbuf))
        scontext_len = sizeof(stackbuf) - 1;

    copy_bytes(stackbuf, scontext, scontext_len);
    stackbuf[scontext_len] = '\0';

    while (scontext_len > 0 &&
          (stackbuf[scontext_len - 1] == '\n' ||
           stackbuf[scontext_len - 1] == '\r' ||
           stackbuf[scontext_len - 1] == ' ')) {
        stackbuf[--scontext_len] = '\0';
    }

    if (!scontext_len)
        return -EINVAL;

    zero_bytes(ctx_buf, sizeof(ctx_buf));

    /* Convert string to struct context using clean policydb */
    rc = string_to_context_struct_fn(policydb, sidtab, stackbuf, ctx, 0);
    if (rc)
        return rc;

    /* Convert struct context to SID using clean sidtab */
    rc = sidtab_context_to_sid_fn(sidtab, ctx, out_sid);

    if (context_destroy_fn)
        context_destroy_fn(ctx);

    return rc;
}

static int clean_compute_av(u32 ssid, u32 tsid, u16 tclass, struct av_decision *avd)
{
    struct policydb *policydb = (struct policydb *)READ_ONCE(g_clean_policydb);
    struct sidtab *sidtab = (struct sidtab *)READ_ONCE(g_clean_sidtab);
    struct context *scontext, *tcontext;

    if (!policydb || !sidtab || !sidtab_search_fn || !context_struct_compute_av_fn || !avd)
        return -EINVAL;

    /* On 4.14 evergo-r-oss, sidtab_search directly returns struct context * */
    scontext = sidtab_search_fn(sidtab, ssid);
    tcontext = sidtab_search_fn(sidtab, tsid);
    if (!scontext || !tcontext)
        return -EINVAL;

    zero_bytes(avd, sizeof(*avd));
    avd->allowed = 0;
    avd->auditallow = 0;
    avd->auditdeny = 0xffffffff;
    avd->seqno = KP_AVD_CLEAN_SEQNO;
    avd->flags = 0;

    /* Pure pointer passing - completely dereference-free! */
    context_struct_compute_av_fn(policydb, scontext, tcontext, tclass, avd, NULL);
    avd->seqno = KP_AVD_CLEAN_SEQNO;
    return 0;
}

/* Independent Policydb & Sidtab Initialization */
static void try_load_clean_policy_and_sidtab(void)
{
    struct policy_file fp;
    struct policydb *pdb;
    struct sidtab *sidtab;
    void *blob = READ_ONCE(g_clean_policy_blob);
    size_t len = READ_ONCE(g_clean_policy_len);
    int rc;

    if (READ_ONCE(g_clean_ready) || !blob || !len)
        return;
    if (!policydb_read_fn || !sidtab_init_fn || !policydb_load_isids_fn || !vmalloc_fn)
        return;

    pdb = (struct policydb *)vmalloc_fn(CLEAN_POLICYDB_ALLOC_SIZE);
    sidtab = (struct sidtab *)vmalloc_fn(CLEAN_SIDTAB_ALLOC_SIZE);
    if (!pdb || !sidtab) {
        if (pdb) vfree_fn(pdb);
        if (sidtab) vfree_fn(sidtab);
        return;
    }

    zero_bytes(pdb, CLEAN_POLICYDB_ALLOC_SIZE);
    zero_bytes(sidtab, CLEAN_SIDTAB_ALLOC_SIZE);

    /* Initialize the clean sidtab */
    rc = sidtab_init_fn(sidtab);
    if (rc) {
        pr_warn("[selinux_hook] sidtab_init failed rc=%d\n", rc);
        goto fail;
    }

    fp.data = (char *)blob;
    fp.len = len;

    /* Parse clean policydb blob */
    rc = policydb_read_fn(pdb, &fp);
    if (rc) {
        pr_warn("[selinux_hook] policydb_read failed rc=%d\n", rc);
        goto fail;
    }

    /* Populate initial SIDs into clean sidtab */
    rc = policydb_load_isids_fn(pdb, sidtab);
    if (rc) {
        pr_warn("[selinux_hook] policydb_load_isids failed rc=%d\n", rc);
        if (policydb_destroy_fn) policydb_destroy_fn(pdb);
        goto fail;
    }

    WRITE_ONCE(g_clean_policydb, pdb);
    WRITE_ONCE(g_clean_sidtab, sidtab);
    WRITE_ONCE(g_clean_ready, true);
    pr_info("[selinux_hook] Clean policydb (%px) and sidtab (%px) ready!\n", pdb, sidtab);
    return;

fail:
    if (sidtab_destroy_fn) sidtab_destroy_fn(sidtab);
    vfree_fn(pdb);
    vfree_fn(sidtab);
}

/* File snapshot logic */
static bool snapshot_policy_file_path(const char *path)
{
    struct file *filp;
    void *data;
    loff_t len, pos;
    ssize_t nread;

    if (!filp_open_fn || !filp_close_fn || !kernel_read_fn || !vfs_llseek_fn || !vmalloc_fn)
        return false;

    filp = filp_open_fn(path, O_RDONLY, 0);
    if (!filp || IS_ERR(filp))
        return false;

    len = vfs_llseek_fn(filp, 0, SEEK_END);
    if (len <= 0 || len > MAGISK_POLICY_MAX_SIZE) {
        filp_close_fn(filp, 0);
        return false;
    }
    vfs_llseek_fn(filp, 0, SEEK_SET);

    data = vmalloc_fn((unsigned long)len);
    if (!data) {
        filp_close_fn(filp, 0);
        return false;
    }

    pos = 0;
    nread = kernel_read_fn(filp, data, (size_t)len, &pos);
    filp_close_fn(filp, 0);
    if (nread != len) {
        if (vfree_fn) vfree_fn(data);
        return false;
    }

    WRITE_ONCE(g_clean_policy_len, (size_t)len);
    WRITE_ONCE(g_clean_policy_blob, data);
    pr_info("[selinux_hook] Clean policy snapshot captured from %s (len=%zu)\n", path, (size_t)len);
    try_load_clean_policy_and_sidtab();
    return true;
}

static void try_capture_clean_policy(void)
{
    if (READ_ONCE(g_clean_policy_blob))
        return;
    if (snapshot_policy_file_path(MAGISK_POLICY_PATH))
        return;
    snapshot_policy_file_path(MAGISK_POLICY_REL_PATH);
}

/* Deferred capture from security_load_policy fallback */
static void after_security_load_policy(hook_fargs4_t *a, void *u)
{
    void *data;
    size_t len;
    void *copy;

    if (READ_ONCE(g_clean_policy_blob) || g_policy_capture_in_progress)
        return;
    if (a && (long)a->ret)
        return;

    g_policy_capture_in_progress = true;

    /* Xiaomi 4.14 uses stateful signature: security_load_policy(state, data, len) */
    data = (void *)a->arg1;
    len = (size_t)a->arg2;

    if (!data || !len || len > MAGISK_POLICY_MAX_SIZE || !vmalloc_fn) {
        g_policy_capture_in_progress = false;
        return;
    }

    /* Do not capture if it already has magisk rules */
    if (contains_magisk(data, len)) {
        g_policy_capture_in_progress = false;
        return;
    }

    copy = vmalloc_fn((unsigned long)len);
    if (copy) {
        copy_bytes(copy, data, len);
        WRITE_ONCE(g_clean_policy_len, len);
        WRITE_ONCE(g_clean_policy_blob, copy);
        pr_info("[selinux_hook] Clean policy captured via security_load_policy len=%zu\n", len);
        try_load_clean_policy_and_sidtab();
    }
    g_policy_capture_in_progress = false;
}

/*
 * =========================================================================
 * Top-Level Interception Handlers (Autonomous & Complete Takeover)
 * =========================================================================
 */

/* Intercept /sys/fs/selinux/access */
static void before_sel_write_access(hook_fargs4_t *a, void *u)
{
    uid_t uid = current_uid();
    char *buf = (char *)a->arg1;
    size_t size = (size_t)a->arg2;
    char scon[256], tcon[256];
    u16 tclass = 0;
    u32 ssid = 0, tsid = 0;
    struct av_decision avd;
    int rc, len;

    if (should_bypass_clean_filter(uid))
        return; /* Let original kernel handler process system/root calls */

    if (!READ_ONCE(g_clean_ready) || !buf || size < 2)
        return;

    /* Parse query string: "scontext tcontext tclass" */
    if (sscanf(buf, "%255s %255s %hu", scon, tcon, &tclass) < 3) {
        a->ret = (uint64_t)-EINVAL;
        a->skip_origin = 1;
        return;
    }

    /* Resolve SIDs on clean policy; if any context contains Magisk, it returns -EINVAL */
    rc = clean_context_to_sid(scon, str_len_safe(scon), &ssid);
    if (rc) {
        a->ret = (uint64_t)rc;
        a->skip_origin = 1;
        return;
    }

    rc = clean_context_to_sid(tcon, str_len_safe(tcon), &tsid);
    if (rc) {
        a->ret = (uint64_t)rc;
        a->skip_origin = 1;
        return;
    }

    /* Compute clean AV decision */
    rc = clean_compute_av(ssid, tsid, tclass, &avd);
    if (rc) {
        a->ret = (uint64_t)rc;
        a->skip_origin = 1;
        return;
    }

    /* Format standard response directly; no patch_response_seqno needed! */
    len = scnprintf(buf, 4080, "%x %x %x %x %u %x",
                   avd.allowed, 0xffffffff,
                   avd.auditallow, avd.auditdeny,
                   avd.seqno, avd.flags);

    a->ret = (uint64_t)len;
    a->skip_origin = 1; /* Completely short-circuit original handler */
}

/* Intercept /sys/fs/selinux/context */
static void before_sel_write_context(hook_fargs4_t *a, void *u)
{
    uid_t uid = current_uid();
    char *buf = (char *)a->arg1;
    size_t size = (size_t)a->arg2;
    u32 sid = 0;
    int rc;

    if (should_bypass_clean_filter(uid))
        return;

    if (!READ_ONCE(g_clean_ready) || !buf || size == 0)
        return;

    /* If context doesn't exist in clean policy, reject with -EINVAL */
    rc = clean_context_to_sid(buf, size, &sid);
    if (rc) {
        a->ret = (uint64_t)rc;
        a->skip_origin = 1;
        return;
    }

    /* Valid context: return size directly */
    a->ret = (uint64_t)size;
    a->skip_origin = 1;
}

/* Intercept selinux_setprocattr */
static void before_selinux_setprocattr(hook_fargs3_t *a, void *u)
{
    const char *name = (const char *)a->arg0;
    const char *value = (const char *)a->arg1;
    size_t size = (size_t)a->arg2;
    uid_t uid = current_uid();
    u32 sid = 0;

    if (should_bypass_clean_filter(uid) || !name || !str_eq_lit(name, "current"))
        return;

    if (!READ_ONCE(g_clean_ready))
        return;

    /* App probing Magisk domain transition via setcon() */
    if (size && value) {
        if (clean_context_to_sid(value, size, &sid) != 0) {
            a->ret = (uint64_t)-EINVAL;
            a->skip_origin = 1; /* Deny transition */
        }
    }
}

/*
 * =========================================================================
 * Fake /sys/fs/selinux/status Handlers
 * =========================================================================
 */
static ssize_t read_clean_status_bytes(char __user *buffer, size_t count, loff_t *ppos)
{
    loff_t pos;
    size_t available;

    if (!ppos || (pos = *ppos) < 0) return -EINVAL;
    if (!count || pos >= (loff_t)sizeof(g_clean_status_bytes)) return 0;

    available = sizeof(g_clean_status_bytes) - (size_t)pos;
    if (count > available) count = available;
    if (compat_copy_to_user(buffer, g_clean_status_bytes + (size_t)pos, (int)count) != (int)count)
        return -EFAULT;

    *ppos = pos + (loff_t)count;
    return (ssize_t)count;
}

static int remap_clean_status_page(struct vm_area_struct *vma)
{
    unsigned long vm_start = *(unsigned long *)((char *)vma + 0);
    unsigned long vm_end = *(unsigned long *)((char *)vma + 8);
    unsigned long vm_flags = *(unsigned long *)((char *)vma + 80);
    unsigned long vm_pgoff = *(unsigned long *)((char *)vma + 152);

    if (vm_pgoff > 0 || (vm_end - vm_start) != 0x1000)
        return -EIO;
    if (vm_flags & VM_WRITE)
        return -EPERM;
    *(unsigned long *)((char *)vma + 80) = vm_flags & ~VM_MAYWRITE;
    return remap_vmalloc_range_fn(vma, g_status_mmap_page, 0);
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

static void record_inline_hook(void *func, void *before, void *after)
{
    if (g_hooks >= (int)(sizeof(g_funcs) / sizeof(g_funcs[0]))) return;
    g_funcs[g_hooks] = func;
    g_hook_befores[g_hooks] = before;
    g_hook_afters[g_hooks] = after;
    g_hooks++;
}

static void uninstall_all_hooks(void)
{
    int i;
    for (i = 0; i < g_hooks; i++) {
        hook_unwrap(g_funcs[i], g_hook_befores[i], g_hook_afters[i]);
    }
    g_hooks = 0;
}

/* Module Init / Exit */
static long init(const char *args, const char *event, void *__user r)
{
    unsigned long addr;

    fill_clean_status_bytes(g_clean_status_bytes);

    vmalloc_fn = kallsyms_lookup_name_by_suffix("vmalloc");
    vmalloc_user_fn = kallsyms_lookup_name_by_suffix("vmalloc_user");
    vfree_fn = kallsyms_lookup_name_by_suffix("vfree");
    filp_open_fn = kallsyms_lookup_name_by_suffix("filp_open");
    filp_close_fn = kallsyms_lookup_name_by_suffix("filp_close");
    kernel_read_fn = kallsyms_lookup_name_by_suffix("kernel_read");
    vfs_llseek_fn = kallsyms_lookup_name_by_suffix("vfs_llseek");
    remap_vmalloc_range_fn = kallsyms_lookup_name_by_suffix("remap_vmalloc_range");

    policydb_read_fn = kallsyms_lookup_name_by_suffix("policydb_read");
    policydb_destroy_fn = kallsyms_lookup_name_by_suffix("policydb_destroy");
    sidtab_init_fn = kallsyms_lookup_name_by_suffix("sidtab_init");
    sidtab_destroy_fn = kallsyms_lookup_name_by_suffix("sidtab_destroy");
    policydb_load_isids_fn = kallsyms_lookup_name_by_suffix("policydb_load_isids");
    sidtab_search_fn = kallsyms_lookup_name_by_suffix("sidtab_search");
    string_to_context_struct_fn = kallsyms_lookup_name_by_suffix("string_to_context_struct");
    sidtab_context_to_sid_fn = kallsyms_lookup_name_by_suffix("sidtab_context_to_sid");
    context_struct_compute_av_fn = kallsyms_lookup_name_by_suffix("context_struct_compute_av");
    context_destroy_fn = kallsyms_lookup_name_by_suffix("context_destroy");
    g_selinux_state = kallsyms_lookup_name_by_suffix("selinux_state");

    pr_info("[selinux_hook] init symbols: sidtab_search=%px compute_av=%px\n",
            sidtab_search_fn, context_struct_compute_av_fn);

    /* Allocate fake status mmap page */
    if (remap_vmalloc_range_fn && vmalloc_user_fn) {
        g_status_mmap_page = vmalloc_user_fn(4096);
        if (g_status_mmap_page) {
            zero_bytes(g_status_mmap_page, 4096);
            copy_bytes(g_status_mmap_page, g_clean_status_bytes, sizeof(g_clean_status_bytes));
        }
    }

    /* 1. Status hooks */
    addr = (unsigned long)kallsyms_lookup_name_by_suffix("sel_read_handle_status");
    if (addr) {
        record_inline_hook((void *)addr, before_sel_read_handle_status, NULL);
        hook_wrap((void *)addr, 4, before_sel_read_handle_status, NULL, NULL);
    }
    addr = (unsigned long)kallsyms_lookup_name_by_suffix("sel_mmap_handle_status");
    if (addr && g_status_mmap_page) {
        record_inline_hook((void *)addr, before_sel_mmap_handle_status, NULL);
        hook_wrap((void *)addr, 2, before_sel_mmap_handle_status, NULL, NULL);
    }

    /* 2. Top-level write operation hooks (Autonomous mode) */
    addr = (unsigned long)kallsyms_lookup_name_by_suffix("sel_write_access");
    if (addr) {
        record_inline_hook((void *)addr, before_sel_write_access, NULL);
        hook_wrap((void *)addr, 3, before_sel_write_access, NULL, NULL);
        pr_info("[selinux_hook] hooked sel_write_access\n");
    }

    addr = (unsigned long)kallsyms_lookup_name_by_suffix("sel_write_context");
    if (addr) {
        record_inline_hook((void *)addr, before_sel_write_context, NULL);
        hook_wrap((void *)addr, 3, before_sel_write_context, NULL, NULL);
        pr_info("[selinux_hook] hooked sel_write_context\n");
    }

    /* 3. Procattr hook */
    addr = (unsigned long)kallsyms_lookup_name_by_suffix("selinux_setprocattr");
    if (addr) {
        record_inline_hook((void *)addr, before_selinux_setprocattr, NULL);
        hook_wrap((void *)addr, 3, before_selinux_setprocattr, NULL, NULL);
        pr_info("[selinux_hook] hooked selinux_setprocattr\n");
    }

    /* 4. Deferred policy capture hook */
    security_load_policy_fn = kallsyms_lookup_name_by_suffix("security_load_policy");
    if (security_load_policy_fn) {
        record_inline_hook((void *)security_load_policy_fn, NULL, after_security_load_policy);
        hook_wrap((void *)security_load_policy_fn, 3, NULL, after_security_load_policy, NULL);
    }

    /* Try to snapshot right now */
    try_capture_clean_policy();

    pr_info("[selinux_hook] module loaded, %d hooks installed\n", g_hooks);
    return 0;
}

static long exit_(void *__user r)
{
    uninstall_all_hooks();

    if (g_status_mmap_page) {
        if (vfree_fn) vfree_fn(g_status_mmap_page);
        g_status_mmap_page = NULL;
    }

    if (g_clean_sidtab) {
        if (sidtab_destroy_fn)
            sidtab_destroy_fn((struct sidtab *)g_clean_sidtab);
        if (vfree_fn)
            vfree_fn(g_clean_sidtab);
        g_clean_sidtab = NULL;
    }

    if (g_clean_policydb) {
        if (policydb_destroy_fn)
            policydb_destroy_fn((struct policydb *)g_clean_policydb);
        if (vfree_fn)
            vfree_fn(g_clean_policydb);
        g_clean_policydb = NULL;
    }

    if (g_clean_policy_blob) {
        if (vfree_fn)
            vfree_fn(g_clean_policy_blob);
        g_clean_policy_blob = NULL;
        g_clean_policy_len = 0;
    }

    WRITE_ONCE(g_clean_ready, false);
    pr_info("[selinux_hook] module unloaded\n");
    return 0;
}

static sel_hook_state_t module_get_working_mode(void)
{
    if (!READ_ONCE(g_clean_ready))
        return SEL_HOOK_STATE_POLICYDB_REQ;
    return SEL_HOOK_STATE_NORMAL;
}

static long control(const char *args, char *__user out_msg, int outlen)
{
    sel_hook_state_t state;
    const char *state_str;
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
        default:
            state_str = "UNKNOWN";
            break;
        }

        len = str_len_safe(state_str);
        if (outlen < len) return -EINVAL;
        if (compat_copy_to_user(out_msg, state_str, (int)len) != (int)len)
            return -EFAULT;

        return 0;
    }

    return -EINVAL;
}

KPM_INIT(init);
KPM_CTL0(control);
KPM_EXIT(exit_);