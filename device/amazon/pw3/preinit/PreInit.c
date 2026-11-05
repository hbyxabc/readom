// SPDX-License-Identifier: Apache-2.0
#define _GNU_SOURCE
#define _FILE_OFFSET_BITS 64
#include "StorageFormat.h"
#include "../report/ReportStop.h"
#include <openssl/sha.h>
#include <sys/ioctl.h>
#include <sys/mount.h>
#include <sys/reboot.h>
#include <linux/fs.h>
#include <sys/stat.h>
#include <sys/statfs.h>
#include <sys/statvfs.h>
#include <sys/sysmacros.h>
#include <sys/utsname.h>
#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <inttypes.h>
#include <limits.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#define MAX_BLOCKS 32
#define MAX_CONF 8192
#define FAT_MOUNT "/pw3-user"
#define CONF_PATH "/pw3-preinit.conf"
struct block { char name[32]; uint64_t sectors, start; bool has_start; };
struct config {
    char system_path[192], release[128];
    unsigned char system_sha[32], init_sha[32], cmdline_sha[32], adb_sha[32];
    uint64_t system_size, offset, sizelimit;
    unsigned seen, block_count;
    bool adb_key;
    struct block blocks[MAX_BLOCKS];
};
static int console_fd = -1, kmsg_fd = -1;
static bool log_channels_tried = false;
/* The log channels, opened by whoever first wants to say something.
 *
 * The nodes are in the ramdisk (pack.LOG_NODES), not made from sysfs, because
 * the mounts that sysfs needs are themselves among the things that can fail --
 * and a stop() before them used to report to nowhere at all: no serial line,
 * and nothing in the kernel log, which is the only channel that reaches a
 * person, since it sits at the fixed physical address on the command line and
 * the stock side reads it back after the next boot. The nodes made from sysfs
 * later replace these, on the tmpfs, and that is what the steady state uses.
 *
 * report() calls this rather than each main() calling it first, so that there
 * is no ordering left to get wrong: the earliest possible failure opens its own
 * channels on the way out. Opening is tried once; a failed open stays failed
 * rather than being retried on every line.
 *
 * O_NONBLOCK is for the *writes*, and it is never taken off again. The open
 * cannot block whatever we ask for -- the kernel sets O_NONBLOCK itself for
 * /dev/console and then restores the caller's flags (tty_io.c, "Don't let
 * /dev/console block") -- but the console is a serial port whose default
 * termios has IXON (tty_std_termios in tty_io.c). An XOFF on the line, or noise
 * on a floating test pad that decodes as one, sets tty->stopped; uart_start()
 * then never calls start_tx(), the ring fills, and a blocking write sleeps in
 * n_tty_write() with no timeout at all. That would hang PID 1 before it could
 * write the kernel log or reach the restart below, which is worse than the
 * silence this change is fixing. With O_NONBLOCK the write returns EAGAIN and
 * the line is lost. That is the right trade: the serial line is a developer's
 * channel, the kernel log is the person's, and kmsg carries the whole text.
 */
static void open_log_channels(void) {
    if (log_channels_tried) return;
    log_channels_tried = true;
    kmsg_fd = open("/dev/kmsg", O_WRONLY | O_CLOEXEC);
    console_fd = open("/dev/console", O_WRONLY | O_CLOEXEC | O_NONBLOCK);
}
/* The first system call of this start that failed, and why.
 *
 * The checks here are written as contracts: a chain of conditions that all have
 * to hold, with one sentence for the chain. What that costs is the reason -- a
 * failed read and a hash that does not match collapse into the same false, and
 * the sentence describes the comparison. A V65 start was refused on 2026-10-21
 * with "extents do not agree" when the truth was a denied stat; the same shape
 * is here, where a read error reads as "SHA256 rejected" and an fstatfs error as
 * "not a FAT filesystem".
 *
 * Only stop() says it. report() is also the progress log, and gluing an earlier
 * harmless failure onto every later line would be worse than saying nothing. */
static const char *fault_call;
static char fault_path[128];
static int fault_why;
static void note(const char *call, const char *path) {
    if (fault_call) return;
    fault_call = call;
    fault_why = errno;
    snprintf(fault_path, sizeof(fault_path), "%s", path ? path : "(a descriptor)");
}
/* Used by the mapper headers, which the host tests compile too; there the hook
 * is the no-op they define for themselves. */
#define PW3_NOTE(call, path) note((call), (path))

static void report(const char *message) {
    open_log_channels();
    /* The kernel log first: it is the one that gets back to a person, and the
     * console write below can be refused or short. */
    if (kmsg_fd >= 0) dprintf(kmsg_fd, "<3>pw3-preinit: %s\n", message);
    if (console_fd >= 0) dprintf(console_fd, "pw3-preinit: %s\n", message);
}
/* How long a failed start stays on the screen before the device restarts
 * itself. Nothing here can draw on the panel, so the last thing the user sees
 * is the launcher's starting screen, which already says the Kindle may restart
 * itself back to its own system within a few minutes. Waiting for ever instead
 * left the only way out as holding the power button for forty seconds, and
 * someone whose whole toolkit is a USB cable has no reason to know that the
 * wait is pointless. Two minutes is long enough to read the screen and to
 * catch the device over USB while the kernel log is still in memory. */
#define STOP_SECONDS 120
/* The report area's block device, once it has been mapped (set in
 * TestFileInit.h), and empty before that.
 *
 * A start that refuses to go on is the one the owner has no other way to hear
 * about. The launcher's screen says the Kindle may restart itself back to its
 * own system within a few minutes, and that is all it says; the reason is in
 * the kernel log, which goes with the kernel. So the reason is also written
 * into the area, where the next tap reads it (installer/install/install.c) --
 * that tap can install the system image again when that is what was wrong,
 * instead of handing over to the same refusal for ever (docs/known-issues.md,
 * 七).
 *
 * Most of the stops in this program happen before the area is mapped, and
 * those write nothing: a stop with nowhere to write is still a stop, and the
 * one refusal a tap can act on comes after the mapping. */
static char report_node[64];
/* In .bss and not on the stack: this runs on a path that is already failing,
 * and 64 KiB there is not what PID 1 should spend its last call on. */
static unsigned char report_area[PW3_REPORT_BYTES];
static void report_stop(const char *message) {
    if (!report_node[0]) return;
    /* Said in the kernel log too, because an area that was not written cannot
     * carry the news that it was not written (the same reason BootReport.cpp
     * has for its own line). */
    report(pw3_report_write_stop(report_node, message, report_area, sizeof(report_area))
           ? "the reason above is also in the report area"
           : "the reason above could not be written to the report area");
}
__attribute__((noreturn)) static void stop(const char *message) {
    if (fault_call) {
        char line[480];
        snprintf(line, sizeof(line), "%s; first failed system call this start: %s %s: %s",
                 message, fault_call, fault_path, strerror(fault_why));
        report(line);
        report_stop(line);
    } else {
        report(message);
        report_stop(message);
    }
    report("STOPPED in the new kernel; the device restarts itself back to the stock system.");
    sync();
    for (unsigned left = STOP_SECONDS; left; --left) sleep(1);
    reboot(RB_AUTOBOOT);
    report("the restart was refused; holding the power button for 40 seconds is the way back.");
    for (;;) pause();
}
static bool decimal(const char *s, uint64_t *out) {
    char *end;
    unsigned long long v;
    if (!*s) return false;
    for (const char *p = s; *p; ++p) if (*p < '0' || *p > '9') return false;
    errno = 0; v = strtoull(s, &end, 10);
    if (errno || *end) return false;
    *out = v; return true;
}
static bool hex_sha(const char *s, unsigned char out[32]) {
    if (strlen(s) != 64) return false;
    for (int i = 0; i < 32; ++i) {
        unsigned v = 0;
        for (int j = 0; j < 2; ++j) {
            unsigned char c = (unsigned char)s[2 * i + j];
            unsigned d = c >= '0' && c <= '9' ? c - '0' : c >= 'a' && c <= 'f' ? c - 'a' + 10 : 16;
            if (d == 16) return false;
            v = (v << 4) | d;
        }
        out[i] = (unsigned char)v;
    }
    return true;
}
static bool safe_component(const char *s) {
    if (!*s || !strcmp(s, ".") || !strcmp(s, "..")) return false;
    for (; *s; ++s) if (!((*s >= 'a' && *s <= 'z') || (*s >= 'A' && *s <= 'Z') ||
        (*s >= '0' && *s <= '9') || *s == '_' || *s == '-' || *s == '.')) return false;
    return true;
}
static bool safe_release(const char *s) {
    if (!*s) return false;
    for (; *s; ++s) if (!((*s >= 'a' && *s <= 'z') || (*s >= 'A' && *s <= 'Z') ||
        (*s >= '0' && *s <= '9') || *s == '_' || *s == '-' || *s == '.' || *s == '+')) return false;
    return true;
}
static bool safe_path(const char *s) {
    char copy[192], *save = NULL, *part;
    if (!*s || *s == '/' || strlen(s) >= sizeof(copy) || strstr(s, "//") || s[strlen(s)-1] == '/') return false;
    strcpy(copy, s);
    for (part = strtok_r(copy, "/", &save); part; part = strtok_r(NULL, "/", &save))
        if (!safe_component(part)) return false;
    return true;
}
static bool block_name(const char *s) {
    if (!strcmp(s, "mmcblk0")) return true;
    if (strncmp(s, "mmcblk0", 7)) return false;
    s += 7;
    if (*s == 'p') ++s;
    else if (!strncmp(s, "boot", 4)) s += 4;
    else if (!strcmp(s, "rpmb")) return true;
    else return false;
    if (!*s) return false;
    for (; *s; ++s) if (*s < '0' || *s > '9') return false;
    return true;
}
/* The call that failed is recorded here because this is where it stops being
 * visible: every caller turns `false` into a judgement about the value it was
 * after -- a configuration rejected, a layout that differs, a command line that
 * is not ours (TestFileInit.h) -- and a read that never happened then reads as a
 * value that disagreed. */
static bool read_text(const char *path, char *buf, size_t cap) {
    int fd = open(path, O_RDONLY | O_CLOEXEC);
    ssize_t n;
    if (fd < 0) { note("open", path); return false; }
    n = read(fd, buf, cap - 1);
    if (n < 0) { note("read", path); close(fd); return false; }
    if ((size_t)n == cap - 1) { close(fd); return false; }
    close(fd); buf[n] = 0;
    while (n && (buf[n-1] == '\n' || buf[n-1] == '\r' || buf[n-1] == ' ')) buf[--n] = 0;
    return true;
}
static bool sysnum(const char *name, const char *field, uint64_t *value) {
    char path[160], buf[64];
    if (snprintf(path, sizeof(path), "/sys/class/block/%s/%s", name, field) >= (int)sizeof(path)) return false;
    return read_text(path, buf, sizeof(buf)) && decimal(buf, value);
}
static bool parse_config(const char *path, struct config *cfg) {
    char data[MAX_CONF], *save = NULL, *line;
    memset(cfg, 0, sizeof(*cfg));
    if (!read_text(path, data, sizeof(data))) return false;
    for (line = strtok_r(data, "\n", &save); line; line = strtok_r(NULL, "\n", &save)) {
        char *eq = strchr(line, '='); unsigned bit = 0;
        if (!eq || eq == line) return false;
        *eq++ = 0;
        if (!strcmp(line, "schema")) { bit = 1U; if (strcmp(eq, "1")) return false; }
        else if (!strcmp(line, "system_path")) { bit = 2U; if (!safe_path(eq)) return false; strcpy(cfg->system_path, eq); }
        else if (!strcmp(line, "system_size")) { bit = 4U; if (!decimal(eq, &cfg->system_size) || cfg->system_size < (1U<<20) || cfg->system_size > UINT32_MAX || cfg->system_size % 512) return false; }
        else if (!strcmp(line, "system_sha256")) { bit = 8U; if (!hex_sha(eq, cfg->system_sha)) return false; }
        else if (!strcmp(line, "init_sha256")) { bit = 16U; if (!hex_sha(eq, cfg->init_sha)) return false; }
        else if (!strcmp(line, "cmdline_sha256")) { bit = 32U; if (!hex_sha(eq, cfg->cmdline_sha)) return false; }
        else if (!strcmp(line, "kernel_release")) { bit = 64U; if (!safe_release(eq) || strlen(eq) >= sizeof(cfg->release) || !strstr(eq, "-pw3-android81")) return false; strcpy(cfg->release, eq); }
        else if (!strcmp(line, "fat_offset")) { bit = 128U; if (!decimal(eq, &cfg->offset) || cfg->offset % 512) return false; }
        else if (!strcmp(line, "fat_sizelimit")) { bit = 256U; if (!decimal(eq, &cfg->sizelimit) || cfg->sizelimit % 512) return false; }
        else if (!strcmp(line, "adb_key_sha256")) { bit = 512U; cfg->adb_key = strcmp(eq, "none") != 0; if (cfg->adb_key && !hex_sha(eq, cfg->adb_sha)) return false; }
        else if (!strcmp(line, "block")) {
            char *a = strchr(eq, ':'), *b;
            struct block *v;
            if (!a || cfg->block_count == MAX_BLOCKS) return false;
            *a++ = 0; b = strchr(a, ':'); if (!b) return false; *b++ = 0;
            if (!block_name(eq) || strlen(eq) >= sizeof(cfg->blocks[0].name)) return false;
            for (unsigned i = 0; i < cfg->block_count; ++i) if (!strcmp(eq, cfg->blocks[i].name)) return false;
            v = &cfg->blocks[cfg->block_count++]; strcpy(v->name, eq);
            if (!decimal(a, &v->sectors) || !v->sectors || v->sectors > INT64_MAX / 512) return false;
            v->has_start = strcmp(b, "-") != 0;
            if (v->has_start != (strncmp(eq, "mmcblk0p", 8) == 0)) return false;
            if (v->has_start && !decimal(b, &v->start)) return false;
        } else return false;
        if (bit && (cfg->seen & bit)) return false;
        cfg->seen |= bit;
    }
    if (cfg->seen != 1023U) return false;
    bool disk = false, user = false;
    uint64_t disk_size = 0, user_start = 0, user_size = 0;
    for (unsigned i = 0; i < cfg->block_count; ++i) {
        struct block *b = &cfg->blocks[i];
        if (!strcmp(b->name, "mmcblk0")) { disk = !b->has_start; disk_size = b->sectors; }
        if (!strcmp(b->name, "mmcblk0p4")) { user = b->has_start; user_start = b->start; user_size = b->sectors; }
    }
    if (!(disk && user && user_start < disk_size && user_size <= disk_size - user_start &&
          cfg->offset < user_size * 512 && (!cfg->sizelimit || cfg->sizelimit <= user_size * 512 - cfg->offset)))
        return false;
    /* The partitions of the stock system are set read only, p4 is left writable,
     * and the kernel keeps that flag per block device, not per sector: a p4 that
     * shared sectors with one of them would be a way through the protection,
     * since a write to the image files reaches those sectors by the other name.
     * This device's table does not overlap, which is why it is worth saying so:
     * a layout that does is not one this port will write to. */
    for (unsigned i = 0; i < cfg->block_count; ++i) {
        struct block *b = &cfg->blocks[i];
        if (!b->has_start || !strcmp(b->name, "mmcblk0p4"))
            continue;
        if (b->start < user_start + user_size && user_start < b->start + b->sectors)
            return false;
    }
    return true;
}
static bool only_pseudo_mounts(void) {
    char data[16384], *save = NULL, *line;
    if (!read_text("/proc/self/mountinfo", data, sizeof(data))) return false;
    for (line = strtok_r(data, "\n", &save); line; line = strtok_r(NULL, "\n", &save)) {
        char type[32], *sep = strstr(line, " - ");
        if (!sep || sscanf(sep + 3, "%31s", type) != 1) return false;
        if (strcmp(type, "rootfs") && strcmp(type, "ramfs") && strcmp(type, "tmpfs") &&
            strcmp(type, "proc") && strcmp(type, "sysfs") && strcmp(type, "devpts") && strcmp(type, "devtmpfs")) return false;
    }
    return true;
}
static bool mkdir_ram(const char *path, mode_t mode) {
    struct stat st;
    if (mkdir(path, mode) && errno != EEXIST) return false;
    return lstat(path, &st) == 0 && S_ISDIR(st.st_mode);
}
static bool node_from_sysfs(const char *sysdev, const char *node, mode_t type) {
    char buf[64], *colon; uint64_t maj, min; struct stat st;
    if (!read_text(sysdev, buf, sizeof(buf)) || !(colon = strchr(buf, ':'))) return false;
    *colon++ = 0;
    if (!decimal(buf, &maj) || !decimal(colon, &min) || maj > 4095 || min > 1048575) return false;
    dev_t dev = makedev((unsigned)maj, (unsigned)min);
    if (mknod(node, type | 0600, dev) && errno != EEXIST) return false;
    return lstat(node, &st) == 0 && (st.st_mode & S_IFMT) == type && st.st_rdev == dev;
}
static bool block_node(const char *name, char path[128]) {
    char sysdev[160];
    if (snprintf(sysdev, sizeof(sysdev), "/sys/class/block/%s/dev", name) >= (int)sizeof(sysdev) ||
        snprintf(path, 128, "/dev/block/%s", name) >= 128) return false;
    return node_from_sysfs(sysdev, path, S_IFBLK);
}
static bool readonly_fd(int fd) {
    int one = 1, value = 0;
    return ioctl(fd, BLKROSET, &one) == 0 && ioctl(fd, BLKROGET, &value) == 0 && value == 1;
}
/* `read_complete`, when a caller asks for it, says whether the whole of
 * `expected_size` was read and a digest computed: that is, whether a false
 * return means "this is not that image" or "this could not be read".
 *
 * The two have to be told apart now that the stock side acts on the first --
 * a refusal naming the image makes the next tap install it again
 * (installer/install/install.c). Reporting a read error as a mismatch would
 * have it throw away an image that is in fact intact and then ask for 196 MB
 * it may have no way to fetch, where before this the next tap simply read the
 * image again and carried on. An image longer than it should be counts as
 * not-read rather than as a mismatch: the mapped device is exactly
 * `cfg.system_size`, so that says the mapping is wrong, not the content. */
static bool sha_fd(int fd, uint64_t expected_size, const unsigned char expected[32], bool *read_complete) {
    unsigned char buf[65536], digest[32]; SHA256_CTX ctx; uint64_t total = 0;
    if (read_complete) *read_complete = false;
    if (lseek(fd, 0, SEEK_SET) != 0 || !SHA256_Init(&ctx)) return false;
    for (;;) {
        ssize_t n = read(fd, buf, sizeof(buf));
        if (n < 0 && errno == EINTR) continue;
        if (n < 0) { note("read", NULL); return false; }
        if (!n) break;
        if (total > expected_size || (uint64_t)n > expected_size - total || !SHA256_Update(&ctx, buf, (size_t)n)) return false;
        total += (uint64_t)n;
    }
    if (total != expected_size || !SHA256_Final(digest, &ctx)) return false;
    if (read_complete) *read_complete = true;
    return !memcmp(digest, expected, 32);
}
static bool hash_regular(const char *path, const unsigned char hash[32]) {
    struct stat st; int fd = open(path, O_RDONLY | O_CLOEXEC | O_NOFOLLOW); bool ok;
    if (fd < 0) return false;
    ok = fstat(fd, &st) == 0 && S_ISREG(st.st_mode) && st.st_size > 0 && sha_fd(fd, (uint64_t)st.st_size, hash, NULL);
    close(fd); return ok;
}
static bool mounted_readonly(const char *path, unsigned long magic, bool noexec, bool nosuid) {
    struct statfs fs; struct statvfs flags;
    return statfs(path, &fs) == 0 && (uint32_t)fs.f_type == magic && statvfs(path, &flags) == 0 &&
        (flags.f_flag & ST_RDONLY) && ((flags.f_flag & ST_NOEXEC) != 0) == noexec &&
        (flags.f_flag & ST_NODEV) && ((flags.f_flag & ST_NOSUID) != 0) == nosuid;
}
/* The one entry this program has. The RAM pre-init main and the read-only
   host-test main that used to stand beside it went with the ram_boot=1 mode
   on 2026-10-29, and with them lock_physical, cmdline_ok, loop_name and
   attach_loop, which nothing else called. Everything above is shared with
   the entry below and stays. */
#include "TestFileInit.h"
