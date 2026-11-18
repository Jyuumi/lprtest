
#define _GNU_SOURCE

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>
#include <errno.h>
#include <time.h>
#include <unistd.h>
#include <fcntl.h>
#include <signal.h>
#include <dirent.h>
#include <sys/stat.h>
#include <sys/statvfs.h>
#include <sys/ioctl.h>
#include <sys/types.h>
#include <sys/vfs.h>
#include <linux/major.h>
#include <linux/fs.h>

#define FUSE_SUPER_MAGIC 0x65735546

#define CHUNK_DWORDS (0x40000u)
#define CHUNK_SIZE   (CHUNK_DWORDS * 4u)
#define MIB          (1048576.0)
#define FILE_CHUNKS  2048u
#define HUT_FMT      "%s" DIRSEP_STR "HUT%05d.BIN"
#define DIRSEP       '/'
#define DIRSEP_STR   "/"
#define FREE_MARGIN  (8u * 1024u * 1024u)
#define PROG_NAME    "lprtest"

static const char *S_BANNER =
    "┏━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┓\n"
    "┃ Linux Partition Reliability Test Tool ┃\n"
    "┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛\n";
static const char *S_USAGE =
    "\nCommand line usage:\n"
    " %s %s [Y/N]\n"
    "\n <target-dir> is the mount point/directory to test; test data\n"
    "     will be written there. A number selects a removable disk\n"
    "     [Y/N] = verify right after writing; default is verify\n";
static const char *S_PROMPT_TARGET =
    "Enter target directory (Enter to continue, Ctrl-C to exit): ";
static const char *S_PROMPT_YN = "Verify immediately after writing? [Y/N]: ";
static const char *S_PROMPT_ROUNDS = "Number of test rounds (write+verify = one round): ";
static const char *S_ROUND_START = "\n *** Round %d of %d ***\n\n";
static const char *S_DRIVE_DETAIL = "\nDrive [%s] details\n===========================================\n";
static const char *S_DRIVE_NG = "\nCannot get drive info. Is the path correct?\n";
static const char *S_NAME = "Device name: ";
static const char *S_VER  = "Version     : ";
static const char *S_TYPE = "Device type: ";
static const char *S_TYPE_FIXED = "Fixed disk";
static const char *S_TYPE_REMOVE = "Removable disk";
static const char *S_REPORT_CAP = "Reported size: ";
static const char *S_AVAIL = "Available size: ";
static const char *S_EXIST_STOP = "\nTest data already exists on target disk. Nothing to do!\n";
static const char *S_EXIST_VERIFY = "\rTest data already exists. Going straight to verify!\n\n";
static const char *S_CREATE_FAIL = "\n\nFailed to create file %s!\n";
static const char *S_WRITE_FAIL = "\n\nFailed to write to file %s!\n";
static const char *S_PROG_WRITE =
    "\rWriting    %8u MB %8.2f MB/s %8.2f MB/s %8u MB  %02d:%02d:%02d    ";
static const char *S_PROG_VERIFY =
    "\rVerifying  %8u MB %8.2f MB/s %8.2f MB/s %8u MB  %02d:%02d:%02d    ";
static const char *S_PROG_HEAD =
    "           Position   Current MB/s  Average MB/s   Free MB      Remain\n";
static const char *S_DATA_ERROR = "\rBAD DATA   %8u MB\n";
static const char *S_WRITE_DONE =
    "\rWrite done %8u MB        - MB/s %8.2f MB/s        - MB  --:--:--    \n";
static const char *S_VERIFY_DONE =
    "\rVerified   %8u MB        - MB/s %8.2f MB/s        - MB  --:--:--    \n\n";
static const char *S_GEN_DONE = "\nTest data files created. You may verify them later.\n";
static const char *S_OPEN_READ_FAIL = "\n\nFailed to open file %s for reading!\n";
static const char *S_VERIFY_BAD = "Verification FAILED: %u MB of data is corrupt. Mind your data!\n\n";
static const char *S_VERIFY_BAD_RO = "Verification FAILED: %u MB corrupt (%u MB unreadable). Mind your data!\n\n";
static const char *S_VERIFY_OK = "All test data verified correct. PASSED!\n\n";
static const char *S_DEL_FAIL = "Failed to delete test file %s!\n\n";
static const char *S_PRESS_ENTER = "\nFinished. Press Enter to exit...";
static const char *S_DRIVE_LIST = "Available target list (* = removable disk):\n\n";
static const char *S_DEL_FILES = "Deleting used test data files...\n\n";
static const char *S_PROMPT_NEXT = "Data errors found. Continue with next round? [Y/N]: ";
static const char *S_SUM_ALL_OK = "Test finished! %u round(s) run, all passed. No problems found!\n\n";
static const char *S_SUM_SOME_OK = "Test finished! %u round(s) run, only %u passed. Disk may be unstable!\n\n";
static const char *S_SUM_ALL_BAD = "Test finished! %u round(s) run, none passed. Disk has problems!\n\n";
static const char *S_SUM_ABORT = "Test finished! %u round(s) run, error in round %u. Ended early!\n\n";
static const char *S_READ_ERROR = "\rREAD FAIL  %8u MB\n";
static const char *S_USER_BREAK =
    "\rUser break %8u MB        - MB/s %8.2f MB/s        - MB  --:--:--    \n";
static const char *S_VERIFY_EARLY = "Verification ended early. No problems found so far!\n\n";
static const char *S_NO_SPACE =
    "\rNo space\n\nNot enough space for test data. Delete some files and retry!\n";

static uint32_t g_s0, g_s1, g_s2, g_s3;

static void prng_reset(void)
{
    g_s0 = 0x159A55E5u;
    g_s1 = 0x1F123BB5u;
    g_s2 = 0x05491333u;
    g_s3 = 0xDCA345EAu;
}

static inline uint32_t prng_next(void)
{
    uint32_t t = (g_s0 << 11) ^ g_s0;
    uint32_t n = g_s3 ^ ((((g_s3 >> 11) ^ t) >> 8)) ^ t;
    g_s0 = g_s1;
    g_s1 = g_s2;
    g_s2 = g_s3;
    g_s3 = n;
    return n;
}

static void fill_chunk(uint8_t *buf)
{
    uint32_t *p = (uint32_t *)buf;
    for (uint32_t i = 0; i < CHUNK_DWORDS; i++)
        p[i] = prng_next();
}

static volatile sig_atomic_t g_interrupted = 0;
static char g_target[1024];
static bool g_color = false;
static uint64_t g_last_total_mib = 0;
static uint8_t *g_chunk_status = NULL;
static uint64_t g_status_cap = 0;

#define ST_OK       1
#define ST_MISMATCH 2
#define ST_READFAIL 3

#define C_RED    (g_color ? "\x1b[31m" : "")
#define C_GREEN  (g_color ? "\x1b[32m" : "")
#define C_YELLOW (g_color ? "\x1b[33m" : "")
#define C_RESET  (g_color ? "\x1b[0m" : "")

static void record_chunk_status(uint64_t mib, uint8_t st)
{
    if (mib == 0)
        return;
    if (mib >= g_status_cap) {
        uint64_t ncap = g_status_cap ? g_status_cap * 2 : 256;
        while (mib >= ncap)
            ncap *= 2;
        g_chunk_status = realloc(g_chunk_status, ncap);
        if (!g_chunk_status) {
            g_status_cap = 0;
            return;
        }
        memset(g_chunk_status + g_status_cap, 0, ncap - g_status_cap);
        g_status_cap = ncap;
    }
    uint8_t cur = g_chunk_status[mib];
    if (st == ST_READFAIL || (st == ST_MISMATCH && cur < ST_MISMATCH) ||
        (st == ST_OK && cur == 0))
        g_chunk_status[mib] = st;
}

static void free_bad_chunks(void)
{
    free(g_chunk_status);
    g_chunk_status = NULL;
    g_status_cap = 0;
}

static void on_sigint(int sig)
{
    (void)sig;
    g_interrupted = 1;

    fflush(stdout);
    _exit(130);
}

static void on_sigterm(int sig)
{
    (void)sig;
    g_interrupted = 1;
}

static void wait_enter(void)
{
    int c;
    while ((c = getchar()) != '\n' && c != EOF)
        ;
}

static double now_sec(void)
{
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + (double)ts.tv_nsec / 1e9;
}

static void fmt_hms(double sec, int *h, int *m, int *s)
{
    if (sec < 0 || sec > 99 * 3600)
        sec = 99 * 3600 - 1;
    long t = (long)sec;
    *h = (int)(t / 3600);
    *m = (int)((t % 3600) / 60);
    *s = (int)(t % 60);
}

static void fmt_gb(double bytes, char *out, size_t n)
{
    snprintf(out, n, "%4.2f GB (%4.2f gB)", bytes / 1073741824.0, bytes / 1e9);
}

struct target_info {
    uint64_t total_bytes;
    uint64_t free_bytes;
    int removable;
    char model[128];
};

static bool get_target_info(const char *dir, struct target_info *ti)
{
    struct statvfs vfs;
    memset(ti, 0, sizeof(*ti));
    if (statvfs(dir, &vfs) != 0)
        return false;
    ti->total_bytes = (uint64_t)vfs.f_blocks * vfs.f_frsize;
    ti->free_bytes  = (uint64_t)vfs.f_bavail * vfs.f_frsize;

    ti->removable = -1;
    FILE *f = fopen("/proc/mounts", "r");
    if (f) {
        char line[1024], dev[256], mp[512];
        while (fgets(line, sizeof(line), f)) {
            if (sscanf(line, "%255s %511s", dev, mp) == 2) {
                size_t l = strlen(mp);
                if ((strcmp(mp, dir) == 0 || (l && mp[l-1] != '/' &&
                     strncmp(mp, dir, l) == 0 && (dir[l] == '/' || dir[l] == 0))) &&
                    strncmp(dev, "/dev/", 5) == 0) {
                    const char *base = dev + 5;
                    char parent[128], sysdir[300];
                    snprintf(parent, sizeof(parent), "%.120s", base);

                    size_t pl = strlen(parent);
                    while (pl && parent[pl-1] >= '0' && parent[pl-1] <= '9') parent[--pl] = 0;
                    if (pl && parent[pl-1] == 'p' && pl > 1 &&
                        (strncmp(parent, "nvme", 4) == 0 || strncmp(parent, "mmcblk", 6) == 0))
                        parent[--pl] = 0;
                    snprintf(sysdir, sizeof(sysdir), "/sys/block/%s", parent);
                    char mdl[96] = "", pth[400];
                    snprintf(pth, sizeof(pth), "%s/removable", sysdir);
                    FILE *fr = fopen(pth, "r");
                    if (fr) {
                        int v = fgetc(fr);
                        ti->removable = (v == '1');
                        fclose(fr);
                    }
                    snprintf(pth, sizeof(pth), "%s/device/model", sysdir);
                    fr = fopen(pth, "r");
                    if (fr) {
                        if (fgets(mdl, sizeof(mdl), fr)) {
                            mdl[strcspn(mdl, "\n")] = 0;
                            size_t ml = strlen(mdl);
                            while (ml && (mdl[ml-1] == ' ' || mdl[ml-1] == '\t')) mdl[--ml] = 0;
                            snprintf(ti->model, sizeof(ti->model), "%s", mdl);
                        }
                        fclose(fr);
                    }
                    break;
                }
            }
        }
        fclose(f);
    }
    return true;
}

struct mnt_entry {
    char dev[128];
    char dir[512];
    char fstype[32];
};

static int scan_targets(struct mnt_entry *entries, int max)
{
    int count = 0;
    FILE *f = fopen("/proc/mounts", "r");
    if (!f)
        return 0;
    char line[1024];
    while (fgets(line, sizeof(line), f) && count < max) {
        char dev[128], dir[512], type[32];
        if (sscanf(line, "%127s %511s %31s", dev, dir, type) != 3)
            continue;

        if (strncmp(dev, "/dev/", 5) != 0)
            continue;
        static const char *skip_fs[] = { "proc", "sysfs", "devtmpfs", "tmpfs", "devpts",
                                         "mqueue", "cgroup", "cgroup2", "securityfs",
                                         "debugfs", "tracefs", "configfs", "fusectl",
                                         "hugetlbfs", "pstore", "bpf", "autofs", "overlay",
                                         "nsfs", "ramfs", NULL };
        bool skip = false;
        for (int i = 0; skip_fs[i]; i++)
            if (strcmp(type, skip_fs[i]) == 0) { skip = true; break; }
        if (skip)
            continue;
        bool dup = false;
        for (int i = 0; i < count; i++)
            if (strcmp(entries[i].dev, dev) == 0) { dup = true; break; }
        if (dup)
            continue;
        snprintf(entries[count].dev, sizeof(entries[count].dev), "%s", dev);
        snprintf(entries[count].dir, sizeof(entries[count].dir), "%s", dir);
        snprintf(entries[count].fstype, sizeof(entries[count].fstype), "%s", type);
        count++;
    }
    fclose(f);
    return count;
}

static bool target_by_number(int num, char *dir, size_t n)
{
    struct mnt_entry entries[128];
    int count = scan_targets(entries, 120);
    int seq = 0;
    for (int i = 0; i < count; i++) {
        struct target_info ti;
        if (get_target_info(entries[i].dir, &ti) && ti.removable == 1) {
            if (++seq == num) {
                snprintf(dir, n, "%s", entries[i].dir);
                return true;
            }
        }
    }
    return false;
}

static int list_targets(void)
{
    struct mnt_entry entries[128];
    int count = scan_targets(entries, 120);

    printf("%s", S_DRIVE_LIST);
    if (count == 0) {
        printf("(no testable disk mount points found)\n");
    }
    int rem_seq = 0;
    for (int i = 0; i < count; i++) {
        struct target_info ti;
        char cap[96];
        if (!get_target_info(entries[i].dir, &ti)) {
            snprintf(cap, sizeof(cap), "    ? GB");
        } else {
            snprintf(cap, sizeof(cap), "%4.0f GB", ti.total_bytes / 1073741824.0);
        }

        bool rem = (ti.removable == 1);
        char mark[16] = "      ";
        if (rem) {
            rem_seq++;
            snprintf(mark, sizeof(mark), " * %2d ", rem_seq);
        }
        printf("%s[%s]  %s  (%s)\n", mark, entries[i].dir, cap, entries[i].fstype);
    }
    printf("\n");
    printf(S_USAGE, PROG_NAME, "<target-dir>");
    return 0;
}

static void hut_path(char *buf, size_t n, int index)
{
    snprintf(buf, n, HUT_FMT, g_target, index);
}

static bool hut_exists(int index)
{
    char path[1200];
    struct stat st;
    hut_path(path, sizeof(path), index);
    return stat(path, &st) == 0 && S_ISREG(st.st_mode);
}

static int open_hut(int index, int mode, bool *odirect)
{
    char path[1200];
    hut_path(path, sizeof(path), index);
    *odirect = false;
    int fd = open(path, mode | O_DIRECT, 0644);
    if (fd >= 0) { *odirect = true; return fd; }
    return open(path, mode, 0644);
}

#define SPEED_WIN 8

struct progress {
    double t_start;
    uint64_t last_pos;
    double last_time;
    double cur_speed;
    double avg_speed;
    const char *fmt;
    bool show_margin;
    uint64_t total_free;

    uint64_t win_pos[SPEED_WIN];
    double win_t[SPEED_WIN];
    int win_head, win_n;
};

static void prog_init(struct progress *pg, const char *fmt, bool show_margin,
                      uint64_t start_free_mib)
{
    memset(pg, 0, sizeof(*pg));
    pg->t_start = pg->last_time = now_sec();
    pg->fmt = fmt;
    pg->show_margin = show_margin;
    pg->total_free = start_free_mib;
    printf("%s", S_PROG_HEAD);
}

static void prog_update(struct progress *pg, uint64_t pos_mib)
{
    double now = now_sec();
    double dt = now - pg->last_time;
    if (pos_mib == pg->last_pos && dt < 0.5)
        return;

    pg->win_pos[pg->win_head] = pos_mib;
    pg->win_t[pg->win_head] = now;
    pg->win_head = (pg->win_head + 1) % SPEED_WIN;
    if (pg->win_n < SPEED_WIN)
        pg->win_n++;
    if (pg->win_n >= 2) {

        int oldest = (pg->win_head + SPEED_WIN - pg->win_n) % SPEED_WIN;
        double wdt = now - pg->win_t[oldest];
        uint64_t wdp = pos_mib - pg->win_pos[oldest];
        if (wdt > 0 && wdp > 0)
            pg->cur_speed = (double)wdp / wdt;
    } else if (dt > 0 && pos_mib > pg->last_pos) {
        pg->cur_speed = (double)(pos_mib - pg->last_pos) / dt;
    }
    double elapsed = now - pg->t_start;
    pg->avg_speed = elapsed > 0 ? (double)pos_mib / elapsed : 0;
    pg->last_pos = pos_mib;
    pg->last_time = now;

    uint64_t margin = 0;
    if (pg->show_margin && pg->total_free > pos_mib)
        margin = pg->total_free - pos_mib;
    else
        margin = 0;
    double remain = pg->cur_speed > 0.01 ? (double)margin / pg->cur_speed : -1;
    int h, m, s;
    fmt_hms(remain, &h, &m, &s);
    printf(pg->fmt, (unsigned)pos_mib, pg->cur_speed, pg->avg_speed,
           (unsigned)margin, h, m, s);
    fflush(stdout);
}

static void prog_final(struct progress *pg, const char *done_fmt, uint64_t pos_mib)
{
    double elapsed = now_sec() - pg->t_start;
    double avg = elapsed > 0 ? (double)pos_mib / elapsed : 0;
    printf(done_fmt, (unsigned)pos_mib, avg);
    fflush(stdout);
}

static int phase_write(uint64_t *written_mib, bool *interrupted)
{
    prng_reset();
    struct statvfs vfs;
    uint64_t free_bytes = 0;
    if (statvfs(g_target, &vfs) == 0)
        free_bytes = (uint64_t)vfs.f_bavail * vfs.f_frsize;
    if (free_bytes > FREE_MARGIN)
        free_bytes -= FREE_MARGIN;
    else
        free_bytes = 0;
    uint64_t free_mib = free_bytes / 1048576u;

    uint8_t *buf = NULL;
    if (posix_memalign((void **)&buf, 4096, CHUNK_SIZE) != 0)
        buf = NULL;
    if (!buf) {
        fprintf(stderr, "Memory allocation failed\n");
        return -1;
    }

    struct progress pg;
    prog_init(&pg, S_PROG_WRITE, true, free_mib);

    int file_idx = 1;
    int chunks_in_file = 0;
    uint64_t total_mib = 0;
    bool odirect = false;
    int fd = open_hut(file_idx, O_WRONLY | O_CREAT | O_TRUNC, &odirect);
    if (fd < 0) {
        char path[1200];
        hut_path(path, sizeof(path), file_idx);
        printf(S_CREATE_FAIL, path);
        free(buf);
        return -1;
    }

    bool force_sync = false;
    {
        struct statfs sfs;
        if (fstatfs(fd, &sfs) == 0 && sfs.f_type == (long)FUSE_SUPER_MAGIC)
            force_sync = true;
    }
    bool bypass = !odirect || force_sync;

    int ret_files = 1;
    for (;;) {

        if (statvfs(g_target, &vfs) == 0) {
            uint64_t avail = (uint64_t)vfs.f_bavail * vfs.f_frsize;
            if (avail <= FREE_MARGIN + CHUNK_SIZE) {

                break;
            }
        }
        if (g_interrupted) {
            prog_final(&pg, S_USER_BREAK, total_mib);
            *interrupted = true;
            break;
        }

        fill_chunk(buf);
        ssize_t w = write(fd, buf, CHUNK_SIZE);
        if (w != (ssize_t)CHUNK_SIZE) {
            if (errno == EINTR && g_interrupted) {

                prog_final(&pg, S_USER_BREAK, total_mib);
                *interrupted = true;
                close(fd);
                free(buf);
                *written_mib = total_mib;
                return ret_files;
            }
            if (errno == ENOSPC) {
                printf("%s", S_NO_SPACE);
            } else {
                char path[1200];
                hut_path(path, sizeof(path), file_idx);
                printf(S_WRITE_FAIL, path);
            }
            close(fd);
            free(buf);
            *written_mib = total_mib;
            return ret_files;
        }

        total_mib++;
        chunks_in_file++;
        if (bypass) {

            if (fdatasync(fd) != 0) {
                if (errno == ENOSPC) {
                    printf("%s", S_NO_SPACE);
                } else {
                    char path[1200];
                    hut_path(path, sizeof(path), file_idx);
                    printf(S_WRITE_FAIL, path);
                }
                close(fd);
                free(buf);
                *written_mib = total_mib;
                return ret_files;
            }
        }
        prog_update(&pg, total_mib);

        if (chunks_in_file >= (int)FILE_CHUNKS) {

            fsync(fd);
            close(fd);
            file_idx++;
            chunks_in_file = 0;
            fd = open_hut(file_idx, O_WRONLY | O_CREAT | O_TRUNC, &odirect);
            if (fd < 0) {
                char path[1200];
                hut_path(path, sizeof(path), file_idx);
                printf(S_CREATE_FAIL, path);
                free(buf);
                *written_mib = total_mib;
                return ret_files;
            }
            ret_files = file_idx;
        }
    }

    fsync(fd);
    prog_final(&pg, S_WRITE_DONE, total_mib);
    close(fd);
    free(buf);
    *written_mib = total_mib;
    return ret_files;
}

static void verify_remount_fuse(void)
{
    char dev[256];
    char line[2048];
    size_t best = 0;
    FILE *f = fopen("/proc/mounts", "r");
    if (!f)
        return;
    while (fgets(line, sizeof(line), f)) {
        char d[256], m[1024], type[64];
        if (sscanf(line, "%255s %1023s %63s", d, m, type) != 3)
            continue;
        if (strcmp(type, "fuseblk") != 0)
            continue;
        size_t ml = strlen(m);

        if (strncmp(g_target, m, ml) == 0 &&
            (g_target[ml] == '/' || g_target[ml] == '\0') &&
            ml > best) {
            best = ml;
            snprintf(dev, sizeof(dev), "%s", d);
        }
    }
    fclose(f);
    if (best == 0)
        return;
    char cmd[1200];
    snprintf(cmd, sizeof(cmd),
             "udisksctl unmount -b '%s' >/dev/null 2>&1 && "
             "udisksctl mount -b '%s' >/dev/null 2>&1",
             dev, dev);
    if (system(cmd) != 0)
        return;
}

static int phase_verify(int file_count, uint64_t *verified_mib,
                        uint64_t *bad_mib, uint64_t *readfail_mib, bool *interrupted)
{
    prng_reset();
    uint8_t *buf = NULL;
    if (posix_memalign((void **)&buf, 4096, CHUNK_SIZE) != 0)
        buf = NULL;
    if (!buf) {
        fprintf(stderr, "Memory allocation failed\n");
        return 2;
    }

    struct progress pg;
    prog_init(&pg, S_PROG_VERIFY, false, 0);

    uint64_t vtotal = 0, bad = 0, rfail = 0;
    int result = 0;

    sync();

    verify_remount_fuse();

    for (int idx = 1; idx <= file_count; idx++) {
        char path[1200];
        hut_path(path, sizeof(path), idx);
        int fd = open(path, O_RDONLY | O_DIRECT);
        bool od = false;
        if (fd >= 0) {

            od = lseek(fd, 0, SEEK_SET) == 0 &&
                 read(fd, buf, CHUNK_SIZE) == (ssize_t)CHUNK_SIZE;
            if (od)
                lseek(fd, 0, SEEK_SET);
            else {
                close(fd);
                fd = open(path, O_RDONLY);
            }
        }
        if (fd < 0)
            fd = open(path, O_RDONLY);
        if (fd < 0) {
            printf(S_OPEN_READ_FAIL, path);
            result = 2;
            break;
        }

        posix_fadvise(fd, 0, 0, POSIX_FADV_DONTNEED);
        for (;;) {
            if (g_interrupted) {
                *interrupted = true;
                break;
            }
            ssize_t r = read(fd, buf, CHUNK_SIZE);
            if (r == 0)
                break;
            if (r < 0) {
                if (errno == EINTR && g_interrupted)
                    continue;
                if (od && errno == EINVAL) {

                    close(fd);
                    fd = open(path, O_RDONLY);
                    if (fd >= 0) {
                        od = false;
                        continue;
                    }
                }

                printf("%s", C_YELLOW);
                printf(S_READ_ERROR, (unsigned)(vtotal + 1));
                printf("%s", C_RESET);
                rfail += 1;
                bad += 1;
                result = 2;
                for (uint32_t i = 0; i < CHUNK_SIZE / 4; i++)
                    (void)prng_next();
                if (lseek(fd, CHUNK_SIZE, SEEK_CUR) < 0)
                    break;
                record_chunk_status(vtotal + 1, ST_READFAIL);
                vtotal += 1;
                prog_update(&pg, vtotal);
                continue;
            }
            uint32_t dwords = (uint32_t)(r / 4);

            const uint32_t *p = (const uint32_t *)buf;
            bool ok = true;
            for (uint32_t i = 0; i < dwords; i++)
                if (p[i] != prng_next())
                    ok = false;

            posix_fadvise(fd, lseek(fd, 0, SEEK_CUR) - r, r, POSIX_FADV_DONTNEED);
            if (!ok) {
                bad++;
                record_chunk_status(vtotal + 1, ST_MISMATCH);
                printf("%s", C_RED);
                printf(S_DATA_ERROR, (unsigned)(vtotal + 1));
                printf("%s", C_RESET);
                result = 1;
            } else {
                record_chunk_status(vtotal + 1, ST_OK);
            }
            vtotal += (uint64_t)(r / 1048576u);
            prog_update(&pg, vtotal);
            if ((size_t)r < CHUNK_SIZE)
                break;
        }
        close(fd);
        if (*interrupted)
            break;

    }

    prog_final(&pg, S_VERIFY_DONE, vtotal);
    *verified_mib = vtotal;
    *bad_mib = bad;
    *readfail_mib = rfail;
    g_last_total_mib = vtotal;
    free(buf);
    return result;
}

static void delete_files(int file_count)
{
    printf("%s", S_DEL_FILES);
    for (int i = 1; i <= file_count; i++) {
        char path[1200];
        hut_path(path, sizeof(path), i);
        if (unlink(path) != 0)
            printf(S_DEL_FAIL, path);
    }
}

static void show_drive_detail(void)
{
    struct target_info ti;
    char cap[96];
    printf(S_DRIVE_DETAIL, g_target);
    if (!get_target_info(g_target, &ti)) {
        printf("%s", S_DRIVE_NG);
        return;
    }
    printf("%s%s\n", S_NAME, ti.model[0] ? ti.model : "(unknown)");
    printf("%s-\n", S_VER);
    printf("%s%s\n", S_TYPE, ti.removable == 1 ? S_TYPE_REMOVE : S_TYPE_FIXED);
    fmt_gb((double)ti.total_bytes, cap, sizeof(cap));
    printf("%s%s\n", S_REPORT_CAP, cap);
    fmt_gb((double)ti.free_bytes, cap, sizeof(cap));
    printf("%s%s\n", S_AVAIL, cap);
    printf("===========================================\n");
}

static int run_round(int round, int rounds, bool do_verify_after, bool *abort_all)
{
    printf(S_ROUND_START, round, rounds);

    bool existing = hut_exists(1);
    int file_count = 1;
    bool interrupted = false;

    free_bad_chunks();
    if (existing) {
        if (do_verify_after) {
            printf("%s", S_EXIST_VERIFY);

            file_count = 1;
            while (hut_exists(file_count + 1))
                file_count++;
        } else {
            printf("%s", S_EXIST_STOP);
            return -1;
        }
    } else {
        uint64_t written_mib = 0;
        file_count = phase_write(&written_mib, &interrupted);
        if (file_count < 0)
            return 0;
        if (!do_verify_after) {
            printf("%s", S_GEN_DONE);
            return -1;
        }
    }

    uint64_t verified_mib = 0, bad_mib = 0, rfail_mib = 0;
    int vr = phase_verify(file_count, &verified_mib, &bad_mib, &rfail_mib, &interrupted);

    if (vr == 0) {
        if (interrupted) {
            printf("%s", S_VERIFY_EARLY);
        } else {
            printf("%s", S_VERIFY_OK);
            delete_files(file_count);
        }
    } else if (vr == 1) {
        if (rfail_mib > 0)
            printf(S_VERIFY_BAD_RO, (unsigned)bad_mib, (unsigned)rfail_mib);
        else
            printf(S_VERIFY_BAD, (unsigned)bad_mib);
    } else {
        if (rfail_mib > 0)
            printf(S_VERIFY_BAD_RO, (unsigned)bad_mib, (unsigned)rfail_mib);
        else if (bad_mib > 0)
            printf(S_VERIFY_BAD, (unsigned)bad_mib);

    }

    if (vr != 0 && !interrupted) {
        printf("%s", S_PROMPT_NEXT);
        fflush(stdout);
        int c = getchar();
        while (c != '\n' && c != EOF)
            c = getchar();
        if (c != 'Y' && c != 'y') {
            *abort_all = true;
            return 0;
        }
    }
    if (interrupted)
        *abort_all = true;
    return vr == 0 ? 1 : 0;
}

static const char *LOGO_OK =
    "   * * *     *       *\n"
    " *       *   *     *\n"
    " *       *   *   *\n"
    " *       *   * *\n"
    " *       *   *   *\n"
    " *       *   *     *\n"
    "   * * *     *       *\n";
static const char *LOGO_NO =
    "*       *     * * *\n"
    "**      *   *       *\n"
    "* *     *   *     *\n"
    "*  *    *   *   *\n"
    "*   *   *   *     *\n"
    "*    *  *   *       *\n"
    "*     * *     * * *\n";

static void print_ending(bool pass, uint64_t total_mib)
{

    const int cells = 14;
    printf("0%% [");
    for (int i = 0; i < cells; i++) {
        uint8_t seg = 0;
        uint64_t seg_start = (uint64_t)((double)total_mib * i / cells) + 1;
        uint64_t seg_end   = (uint64_t)((double)total_mib * (i + 1) / cells);
        for (uint64_t m = seg_start; m <= seg_end && m < g_status_cap; m++)
            if (g_chunk_status[m] > seg)
                seg = g_chunk_status[m];
        const char *col = seg == ST_READFAIL ? C_YELLOW :
                          seg == ST_MISMATCH ? C_RED :
                          seg == ST_OK       ? C_GREEN : "";
        printf("%s%s%s", col, g_color ? "█" : " ", C_RESET);
    }
    printf("] 100%%\n\n");
    printf("%s%s%s", pass ? C_GREEN : C_RED, pass ? LOGO_OK : LOGO_NO, C_RESET);
    printf("%s", S_PRESS_ENTER);
    fflush(stdout);
    wait_enter();
    printf("\n");
}

static bool interactive_select(bool *do_verify, int *rounds)
{
    printf("%s", S_BANNER);
    list_targets();
    printf("%s", S_PROMPT_TARGET);
    fflush(stdout);
    if (scanf("%1023s", g_target) != 1)
        return false;

    {
        bool all_digits = g_target[0] != '\0';
        for (const char *p = g_target; *p; p++)
            if (*p < '0' || *p > '9') { all_digits = false; break; }
        if (all_digits) {
            int num = atoi(g_target);
            char dir[512];
            if (num < 1 || !target_by_number(num, dir, sizeof(dir))) {
                printf("(no removable disk numbered %d)\n", num);
                return false;
            }
            snprintf(g_target, sizeof(g_target), "%s", dir);
        }
    }
    wait_enter();

    show_drive_detail();

    printf("%s", S_PROMPT_YN);
    fflush(stdout);
    int c = getchar();
    wait_enter();
    *do_verify = (c == 'Y' || c == 'y' || c == '\n');

    printf("%s", S_PROMPT_ROUNDS);
    fflush(stdout);
    if (scanf("%d", rounds) != 1)
        *rounds = 1;
    wait_enter();
    return true;
}

int main(int argc, char *argv[])
{
    struct sigaction sa;
    memset(&sa, 0, sizeof(sa));
    sa.sa_handler = on_sigint;
    sigaction(SIGINT, &sa, NULL);
    sa.sa_handler = on_sigterm;
    sigaction(SIGTERM, &sa, NULL);

    signal(SIGXFSZ, SIG_IGN);

    bool do_verify = true;
    int rounds = 1;
    bool verify_only = false;

    g_color = isatty(fileno(stdout));

    if (argc < 2) {

        bool dv;
        int rd = 1;
        if (!interactive_select(&dv, &rd))
            return 1;
        do_verify = dv;
        rounds = rd;
    } else {

        bool all_digits = argv[1][0] != '\0';
        for (const char *p = argv[1]; *p; p++)
            if (*p < '0' || *p > '9') { all_digits = false; break; }
        if (all_digits) {
            int num = atoi(argv[1]);
            if (num < 1 || !target_by_number(num, g_target, sizeof(g_target))) {
                fprintf(stderr, "Error: no removable disk numbered %d\n", num);
                list_targets();
                return 1;
            }
        } else {
            snprintf(g_target, sizeof(g_target), "%s", argv[1]);
        }

        size_t l = strlen(g_target);
        while (l > 1 && g_target[l-1] == '/') g_target[--l] = 0;

        if (argc >= 3 && argv[2][0]) {
            char c = argv[2][0];
            if (c == 'Y' || c == 'y') do_verify = true;
            else if (c == 'N' || c == 'n') do_verify = false;
            else if (c == 'R' || c == 'r') { do_verify = true; verify_only = true; }
            else {
                fprintf(stderr, "Error: unknown mode \"%s\" (Y=write+verify, N=write only, R=verify only)\n", argv[2]);
                return 1;
            }
        }

        if (argc >= 4 && argv[3][0]) {
            int rd = atoi(argv[3]);
            if (rd < 1)
                rd = 1;
            rounds = rd;
        }
        printf("%s", S_BANNER);
    }

    struct stat st;
    if (stat(g_target, &st) != 0 || !S_ISDIR(st.st_mode)) {
        printf("%s", S_DRIVE_NG);
        printf(S_USAGE, PROG_NAME, "<target-dir>");
        return 1;
    }
    show_drive_detail();

    if (verify_only) {

        if (!hut_exists(1)) {
            char path[1200];
            hut_path(path, sizeof(path), 1);
            printf(S_OPEN_READ_FAIL, path);
            return 1;
        }
        int file_count = 1;
        while (hut_exists(file_count + 1))
            file_count++;
        uint64_t v, b, rf;
        bool intr = false;
        int vr = phase_verify(file_count, &v, &b, &rf, &intr);
        if (vr == 0) {
            if (intr) printf("%s", S_VERIFY_EARLY);
            else {
                printf("%s", S_VERIFY_OK);
                delete_files(file_count);
            }
        } else if (vr == 1) {
            printf(S_VERIFY_BAD, (unsigned)b);
        } else if (rf > 0) {

            printf(S_VERIFY_BAD_RO, (unsigned)b, (unsigned)rf);
        }

        print_ending(vr == 0, g_last_total_mib);
        free_bad_chunks();
        return vr == 0 ? 0 : 2;
    }

    unsigned ok_rounds = 0, done_rounds = 0;
    bool abort_all = false;
    for (int r = 1; r <= rounds && !abort_all && !g_interrupted; r++) {
        int rr = run_round(r, rounds, do_verify, &abort_all);
        if (rr < 0) {

            print_ending(true, g_last_total_mib);
            free_bad_chunks();
            return 0;
        }
        if (rr == 1) ok_rounds++;
        done_rounds++;
    }

    if (abort_all && ok_rounds == 0)
        printf(S_SUM_ABORT, done_rounds, done_rounds ? done_rounds : 1);
    else if (ok_rounds == done_rounds && done_rounds > 0)
        printf(S_SUM_ALL_OK, done_rounds);
    else if (ok_rounds == 0)
        printf(S_SUM_ALL_BAD, done_rounds);
    else
        printf(S_SUM_SOME_OK, done_rounds, ok_rounds);

    print_ending(ok_rounds == done_rounds && done_rounds > 0, g_last_total_mib);
    free_bad_chunks();
    return (ok_rounds == done_rounds) ? 0 : 2;
}
