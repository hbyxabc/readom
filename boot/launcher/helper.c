/* SPDX-License-Identifier: GPL-2.0-only */
/* The Android entry's helper, run as root by the launcher script on the stock
 * system: checks the stock system, loads the handoff module, gives it the
 * build's kernel and public initramfs together with what only this device has
 * (ATAGs and a device archive, made from the running system now: devicedata.c),
 * runs the native PM core preflight, then the jump. */
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdint.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/file.h>
#include <sys/klog.h>
#include <sys/mman.h>
#include <time.h>
#include <sys/ioctl.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/sysmacros.h>
#include <sys/types.h>
#include <sys/utsname.h>
#include <sys/wait.h>
#include <unistd.h>
#include "stage_abi.h"
#include "native-abi.h"
#include "engine-guard.h"
#include "sha256.h"
#include "payload.h"
#include "devicedata.h"
#include "userlog.h"
#ifdef PW3_INSTALLER
#include "install.h"
#include "kindle.h"
#include "release.h"
#include "screen.h"
#include "ReportArea.h"
#endif
#if CHECK_PROFILE != 1 && CHECK_PROFILE != 2
#error "Explicit stock or virtual profile required"
#endif
/* Where a run writes what it did. The launcher script is given the same two
 * strings (build_launcher.py), and this is the only place either is written
 * down for the program.
 *
 * The release build -- the only one anybody installs -- writes inside the
 * folder the installer already owns, as one folder per tap with the newest five
 * kept (userlog.h). The other build is made by one host test and nothing else
 * (boot/handoff/tests/run_client_test.py, the virtual profile in QEMU): it has
 * no installer, so no folder is owned, and it writes to the top of the user
 * store and removes nothing -- deleting by prefix at the top of someone's drive
 * is not a thing this project does. That build never reaches a device, and
 * build_entry.py will not make an entry out of it. */
#ifdef PW3_INSTALLER
#define PW3_ANDROID_DIR "/mnt/us/android"
#define PW3_LOG_DIR PW3_ANDROID_DIR "/logs"
#define PW3_OUTPUT_PREFIX PW3_LOG_DIR "/"
#define PW3_LOGS_KEPT 5
#define PW3_REPORT_PATH PW3_ANDROID_DIR "/" PW3_REPORT_NAME
#else
#define PW3_OUTPUT_PREFIX "/mnt/us/pw3-first-kernel-"
#endif
_Static_assert(sizeof(struct pws_native_report)==260,"native report ABI");
_Static_assert(sizeof(void *) == 4 && sizeof(size_t) == 4, "ARM32 required");
_Static_assert(sizeof(struct pws_begin) == 116, "begin ABI");
_Static_assert(sizeof(struct pws_put) == 24, "put ABI");
_Static_assert(sizeof(struct pws_status) == 48, "status ABI");
_Static_assert(sizeof(struct pws_plan_status) == 40, "plan status ABI");
static int output = -1, control = -1, loaded, workspace_created;
static char workspace[128], node[160];
static volatile sig_atomic_t interrupted;
/* Set by a request to stop (SIGTERM, SIGINT, SIGHUP) and never cleared, unlike
 * interrupted, which the 90-second SIGALRM sets too: holding the last screen
 * (kindle_hold_screen) ignores the guard and must not ignore a request. */
static volatile sig_atomic_t terminated;
static unsigned checks;
static int pm_test_changed;
static int restore_pm_test(void);
static int original_boot(void);
static int root_readonly(void);
static void notice(int signal_number) { if (signal_number != SIGALRM) terminated = 1; interrupted = 1; }
static void require(int condition, const char *message);
#ifdef PW3_INSTALLER
/* The installer's screens (installer/install/screen.h): their picture lives in a
 * private directory for the whole run. */
static struct screen screen; static char screen_dir[64]; static int screen_ready, stopping, stop_shown;
/* Returns whether the screen reached the panel. The caller needs to know,
 * because the exit status tells the launcher which of two things to do and may
 * not be guessed: 3 means "the reason is on the screen, add nothing", and every
 * other non-zero status makes the launcher print its own fallback line
 * (launcher-template.sh, finish). A screen that was never drawn -- the screens
 * could not be opened, /tmp had no room for the picture, the failure came
 * before open_screens() -- must therefore not exit 3, or the tap explains
 * itself nowhere at all. */
static int show(enum pw3_screen id) {
    if (!screen_ready) return 0;
#if CHECK_PROFILE == 1
    /* These screens too, not only the installer's: a run that finds the
     * system in place draws one CHECK and then only these, so a finger that
     * was down at that one would leave the rest of the run untaken
     * (kindle_take_touch, kindle.h). */
    kindle_take_touch();
#endif
    if (screen_show(&screen, id, -1, 0)) { printf("PW3_INSTALL cannot show screen %d\n", (int)id); return 0; }
    return 1;
}
/* Stop, with that screen if it is the first stop of this run, and with an exit
 * status that says whether anybody can read the reason. `stop_shown` is the
 * answer for the screen that explains the stop -- not for a screen drawn
 * earlier, because a panel still showing "preparing" explains nothing. */
static void stop_now(enum pw3_screen id) {
    if (!stopping) { stopping = 1; stop_shown = show(id); }
    exit(stop_shown ? 3 : 1);
}
#endif
struct piece { const unsigned char *data; uint32_t bytes; };

static int present(void) {
    FILE *stream = fopen("/proc/modules", "r");
    if (!stream) return -1;
    char line[1024], name[128]; int found = 0;
    while (fgets(line, sizeof(line), stream))
        if (sscanf(line, "%127s", name) == 1 && !strcmp(name, "pw3_first_kernel")) found++;
    int error = ferror(stream); fclose(stream);
    return error ? -1 : found;
}
static int cleanup_module(void) {
    int okay = 1;
    if (control >= 0) {
        if (ioctl(control, PWS_DISCARD, 0)) okay = 0;
        if (close(control)) okay = 0;
        control = -1;
    }
    if (loaded) {
        FILE *stream = fopen("/sys/module/pw3_first_kernel/parameters/live_pages", "r");
        unsigned remaining = ~0u; char extra;
        int pages_valid = stream && fscanf(stream, "%u %c", &remaining, &extra) == 1;
        if (stream) fclose(stream);
        if (!pages_valid || remaining != 0) {
            fprintf(stderr, "PW3_FIRST_KERNEL_CLEANUP page accounting did not return to zero\n");
            okay = 0;
        } else {
            puts("PW3_FIRST_KERNEL_CLEANUP owned_pages=0");
            if (syscall(SYS_delete_module, "pw3_first_kernel", O_NONBLOCK)) okay = 0;
            else loaded = 0;
        }
    }
    return okay;
}
static void cleanup(void) {
    if(pm_test_changed && !restore_pm_test())fprintf(stderr,"Cannot restore pm_test; normal restart resets it\n");
    int module_ok=cleanup_module();
    if (!module_ok) fprintf(stderr,"First-kernel cleanup incomplete; normal restart clears remaining module\n");
    printf("PW3_FIRST_KERNEL_CLEANUP module_unloaded=%d original_boot_verified=%d root_readonly_verified=%d pm_restore_pending=%d\n",module_ok && !loaded && present()==0,original_boot(),root_readonly(),pm_test_changed);
    fflush(stdout);fsync(STDOUT_FILENO);
#if defined(PW3_INSTALLER) && CHECK_PROFILE == 1
    /* A run that stopped with its reason on the screen keeps it there until
     * the reader taps (kindle.h): the launcher that started this script paints
     * the library over the screen about a second after the script exits. After
     * the module is gone and the log is on the disk, so a reader who leaves it
     * for ten minutes is holding nothing but the screen. */
    if (stopping && stop_shown) { kindle_hold_screen(&terminated); fflush(stdout); fsync(STDOUT_FILENO); }
#endif
    if (workspace_created) { if (node[0]) unlink(node); rmdir(workspace); }
#ifdef PW3_INSTALLER
    if (screen_ready) { screen_free(&screen); rmdir(screen_dir); screen_ready = 0; }
#endif
    if (output >= 0) { fsync(output); close(output); output = -1; }
}
static void require(int condition, const char *message) {
    checks++;
    if (condition) return;
    fprintf(stderr, "PW3_FIRST_KERNEL_CHECK_FAIL check=%s errno=%d checks=%u\n", message, errno, checks);
#ifdef PW3_INSTALLER
    stop_now(PW3_SCREEN_STOPPED);
#endif
    exit(1);
}
/* The device data could not be made. One reason is not like the others: this
 * build is for a Paperwhite 3 on one firmware, and someone with a different
 * Kindle can copy the file into their library just the same, since what makes
 * it appear there is the jailbreak, not us. The ordinary screen tells them to
 * restart and tap again, which for them is for ever; E101 says the model or
 * the software version is not supported and that nothing was changed. */
__attribute__((noreturn)) static void device_data_failed(const struct dd_why *why, const char *check) {
    fprintf(stderr, "PW3_DEVICE_DATA %s\n", why->text);
#ifdef PW3_INSTALLER
    if (why->other_device) {
        stop_now(PW3_SCREEN_E101);
    }
#endif
    require(0, check);
    exit(1);   /* require() does not return here */
}
static void checkpoint(const char *name) {
    require(!interrupted, "interrupted_or_deadline");
#if CHECK_PROFILE == 2
    char wanted[64] = {0};
    int fd = open("/test-fault-stage", O_RDONLY | O_CLOEXEC);
    if (fd >= 0) { ssize_t n = read(fd, wanted, sizeof(wanted)-1); close(fd); if (n > 0) wanted[n] = 0; }
    if (!strcmp(wanted, name)) require(0, "virtual_fault_checkpoint");
#else
    (void)name;
#endif
}
static void digest(const unsigned char *data, size_t bytes, unsigned char result[32]) {
    SHA256_CTX ctx; sha256_init(&ctx); sha256_update(&ctx, data, bytes); sha256_final(&ctx, result);
}
static int exact_file(const char *path, const char *expected, size_t bytes) {
    int fd = open(path, O_RDONLY | O_NOFOLLOW | O_CLOEXEC); struct stat st;
    if (fd < 0) return 0;
    if (fstat(fd, &st) || !S_ISREG(st.st_mode) || (size_t)st.st_size != bytes) { close(fd); return 0; }
    unsigned char block[4096], result[32]; SHA256_CTX hash; sha256_init(&hash); size_t total = 0;
    for (;;) {
        ssize_t n = read(fd, block, sizeof(block));
        if (n < 0 && errno == EINTR) continue;
        if (n < 0) { close(fd); return 0; }
        if (!n) break;
        total += (size_t)n; sha256_update(&hash, block, (size_t)n);
    }
    close(fd); sha256_final(&hash, result); char hex[65];
    for (unsigned i = 0; i < 32; i++) snprintf(hex + i*2, 3, "%02x", result[i]);
    return total == bytes && !strcmp(hex, expected);
}
static int original_boot(void) {
#if CHECK_PROFILE == 1
    return exact_file("/sbin/init", "ad624cbad3090bf15e65c8420a4e451ee10fd067a40b1bfe662965e82d932d0a", 1360) &&
        exact_file("/etc/upstart/init.sh", "ad624cbad3090bf15e65c8420a4e451ee10fd067a40b1bfe662965e82d932d0a", 1360) &&
        exact_file("/sbin/init.exe", "9fcbbf735c2fd4d7758ebdbf836c79c61b405867d28d4488d09315f80e21d2cf", 111824);
#else
    return 1;
#endif
}
static int root_readonly(void) {
#if CHECK_PROFILE == 1
    FILE *stream = fopen("/proc/mounts", "r");
    if (!stream) return 0;
    char line[1024], from[256], target[256], type[64], options[256]; int seen = 0, ro = 0;
    while (fgets(line, sizeof(line), stream)) {
        if (sscanf(line, "%255s %255s %63s %255s", from, target, type, options) != 4 || strcmp(target, "/")) continue;
        seen++; ro = 0; char *save = NULL;
        for (char *p = strtok_r(options, ",", &save); p; p = strtok_r(NULL, ",", &save)) if (!strcmp(p, "ro")) ro = 1;
    }
    int error = ferror(stream); fclose(stream); return !error && seen > 0 && ro;
#else
    return 1;
#endif
}
#ifndef PW3_INSTALLER   /* the installer's builds show screen.h's screens */
static void display(const char *message) {
#if CHECK_PROFILE == 1
    pid_t pid = fork(); require(pid >= 0, "display_fork");
    if (!pid) { execl("/usr/sbin/eips", "/usr/sbin/eips", "1", "1", message, (char *)NULL); _exit(127); }
    int status; pid_t got;
    do { got = waitpid(pid, &status, 0); } while (got < 0 && errno == EINTR);
    require(got == pid && WIFEXITED(status) && WEXITSTATUS(status) == 0, "display_exit");
#else
    printf("PW3_FIRST_KERNEL_TEST_DISPLAY %s\n", message);
#endif
}
#endif
static void report(const char *phase, const struct pws_status *s) {
    printf("PW3_FIRST_KERNEL_STAGE phase=%s state=%u payload_pages=%u control_pages=%u collision_pages=%u execute_available=%u\n",
           phase, s->state, s->payload_pages, s->control_pages, s->collision_pages, s->execute_available);
}
static struct pws_status status(unsigned state) {
    struct pws_status s = {0}; require(ioctl(control, PWS_STATUS, &s) == 0, "status_ioctl");
    require(s.version == PWS_VERSION && s.state == state && s.execute_available==1, "state_and_execute_candidate");
    return s;
}
static unsigned live_pages(void) {
    FILE *stream = fopen("/sys/module/pw3_first_kernel/parameters/live_pages", "r"); unsigned n = ~0u; char extra;
    require(stream != NULL, "live_pages_open");
    require(fscanf(stream, "%u %c", &n, &extra) == 1, "live_pages_value"); fclose(stream); return n;
}
static void write_result(const char *filename,const char *text) {
    int fd = openat(output, filename, O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW | O_CLOEXEC, 0600);
    require(fd >= 0, "result_create"); size_t remaining = strlen(text), offset = 0;
    while (remaining) { ssize_t n = write(fd, text + offset, remaining); if (n < 0 && errno == EINTR) continue;
        require(n > 0, "result_write"); offset += (size_t)n; remaining -= (size_t)n; }
    require(fsync(fd) == 0 && close(fd) == 0 && fsync(output) == 0, "result_sync");
}
/* A kernel log, on its way to a folder someone may send to a stranger: only the
 * lines userlog.c allows, with how many were left out. Every build filters the
 * same way: the test entry, which kept the whole log because its folders were
 * read over the cable and never published, went on 2026-10-29.
 * The buffer itself is untouched: the preflight compares the log before the
 * suspend with the log after it, and a filtered comparison would be one that
 * cannot see an error it was not told about. */
/* A file in this run's folder taking a filtered kernel log (userlog.h), opened
 * and closed here because only this program knows which failures matter. Both
 * halves report instead of stopping; the caller decides. */
struct klog_file { struct pw3_klog_out out; FILE *stream; int fd; };
static int klog_begin(struct klog_file *f, const char *filename, const char *source) {
    f->fd = openat(output, filename, O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW | O_CLOEXEC, 0600);
    if (f->fd < 0) return -1;
    f->stream = fdopen(f->fd, "w");
    if (!f->stream) { close(f->fd); return -1; }
    pw3_klog_begin(&f->out, f->stream, source);
    return 0;
}
static int klog_finish(struct klog_file *f) {
    int bad = pw3_klog_end(&f->out);
    if (fflush(f->stream) || fsync(f->fd)) bad = -1;
    if (fclose(f->stream) || fsync(output)) bad = -1;
    return bad;
}
static void write_kernel_log(const char *filename,const char *text) {
    /* This one the preflight owes its folder: both snapshots are what says
     * whether the suspend came back, so failing to write one is failing. */
    struct klog_file f;
    require(klog_begin(&f, filename, "klogctl") == 0, "kernel_log_create");
    pw3_klog_feed(&f.out, text, strlen(text));
    require(klog_finish(&f) == 0, "kernel_log_write");
}
/* What the kernel of the last session said, which on this device is the only
 * way a problem after Android started reaches anyone: both kernels are built
 * with the lab126 printk buffer and the same `log_pos_goal`, so the stock
 * kernel publishes the memory the previous one logged into as /proc/printkbuf.
 * It is the raw ring, not in order -- whoever reads it is told so -- and it is
 * filtered like every other kernel log here.
 *
 * Nothing here can stop a start, and that is the point: this file is last
 * session's courtesy, and the installer has not run yet, so the user store it
 * is written to has not been checked for room for anything (the installer's own
 * check comes later, with E401 and the shortfall on the screen). A start that
 * died here would die before the screen that explains why. So the store is
 * asked for room first and the courtesy is skipped when it is nearly full
 * (pw3_store_has_room), because the files this run cannot do without are
 * written after it and have no way to carry on; and a failure anyway takes the
 * half written file with it and says so in this run's log. */
#define PREVIOUS_KERNEL_LOG "previous-kernel.txt"
#define PREVIOUS_KERNEL_LOG_MAX 262144u
static void save_previous_kernel_log(void) {
#ifdef PW3_INSTALLER
    uint64_t room;
    if (!pw3_store_has_room(PW3_LOG_DIR, PREVIOUS_KERNEL_LOG_MAX, &room)) {
        printf("PW3_PREVIOUS_LOG not_written free=%llu\n", (unsigned long long)room); return;
    }
#endif
    int fd = open("/proc/printkbuf", O_RDONLY | O_NOFOLLOW | O_CLOEXEC);
    if (fd < 0) { printf("PW3_PREVIOUS_LOG absent errno=%d\n", errno); return; }
    struct klog_file f;
    if (klog_begin(&f, PREVIOUS_KERNEL_LOG, "/proc/printkbuf (raw ring, not in order)")) {
        printf("PW3_PREVIOUS_LOG not_written errno=%d\n", errno); close(fd); return;
    }
    /* A read that fails is not the end of the ring. Stopping on both and then
     * writing the file out cleanly presented however much had been collected as
     * the whole of it, with nothing anywhere saying otherwise. */
    char chunk[4096]; size_t total = 0; int source = 0;
    while (total < PREVIOUS_KERNEL_LOG_MAX) {
        ssize_t n = read(fd, chunk, sizeof(chunk));
        if (n < 0 && errno == EINTR) continue;
        if (n < 0) { source = errno; break; }
        if (n == 0) break;
        total += (size_t)n; pw3_klog_feed(&f.out, chunk, (size_t)n);
    }
    close(fd);
    unsigned kept = f.out.kept;
    if (klog_finish(&f)) {
        printf("PW3_PREVIOUS_LOG incomplete errno=%d; removed\n", errno);
        unlinkat(output, PREVIOUS_KERNEL_LOG, 0);
        return;
    }
    if (source)
        printf("PW3_PREVIOUS_LOG partial bytes=%u kept=%u read_errno=%d\n", (unsigned)total, kept, source);
    else
        printf("PW3_PREVIOUS_LOG bytes=%u kept=%u\n", (unsigned)total, kept);
}
#ifdef PW3_INSTALLER
/* What the last Android start left behind: the report area the installer makes
 * on the user store (device/amazon/pw3/report/ReportArea.h), copied into this
 * tap's folder as text. It is the other half of the previous kernel log --
 * that one says what the kernel saw, this one what user space did, which on a
 * release build is otherwise unreachable: no adb, and nothing of
 * sys.usb.config, init.svc.adbd or the refresh counters was ever in a printk
 * ring.
 *
 * The area is read and not cleared. A tap with no Android start since the last
 * one copies the same report again, and `boot=` says which start wrote it, so
 * two folders with the same number are two reads of one report rather than two
 * reports that happen to agree.
 *
 * Filtered line by line like everything else written here (pw3_report_write),
 * and a courtesy on the same terms as the previous kernel log: the installer's
 * space check has not run yet, so a nearly full store keeps its room instead
 * (pw3_store_has_room); nothing in here stops a start; and a half written file
 * is removed and said so in this run's log. */
#define ANDROID_REPORT_LOG "android-report.txt"
/* The greatest boot counter any previous tap recorded. 1 with *boot set, 0 when
 * no previous tap recorded one, -1 when the folders could not be read through
 * (errno says why). The counter is carried as an unsigned rather than folded
 * into a signed return with sentinels, so that every value the writer can
 * produce -- it saturates at UINT32_MAX -- comes through as itself. */
static int previous_report_boot(const char *current, unsigned *boot) {
    const int r = pw3_logs_report_max(PW3_LOG_DIR, current, ANDROID_REPORT_LOG, boot);
    return r < 0 ? -1 : r;
}
static void save_android_report(int found, unsigned before) {
    static unsigned char area[PW3_REPORT_BYTES];
    uint64_t room;
    if (!pw3_store_has_room(PW3_LOG_DIR, PW3_REPORT_BYTES, &room)) {
        printf("PW3_ANDROID_REPORT not_written free=%llu\n", (unsigned long long)room); return;
    }
    int fd = open(PW3_REPORT_PATH, O_RDONLY | O_NOFOLLOW | O_CLOEXEC);
    if (fd < 0) { printf("PW3_ANDROID_REPORT absent errno=%d\n", errno); return; }
    size_t got = 0; int source = 0;
    while (got < sizeof(area)) {
        ssize_t n = read(fd, area + got, sizeof(area) - got);
        if (n < 0 && errno == EINTR) continue;
        if (n < 0) { source = errno; break; }
        if (n == 0) break;
        got += (size_t)n;
    }
    close(fd);
    struct pw3_report rep;
    /* "no valid report" and "the store would not let me read the area" are not
     * the same finding, and the second one is about the store rather than about
     * Android. */
    if (!pw3_report_parse(area, got, &rep)) {
        if (source) printf("PW3_ANDROID_REPORT unreadable bytes=%u errno=%d\n", (unsigned)got, source);
        else printf("PW3_ANDROID_REPORT none bytes=%u\n", (unsigned)got);
        return;
    }
    int out = openat(output, ANDROID_REPORT_LOG, O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW | O_CLOEXEC, 0600);
    if (out < 0) { printf("PW3_ANDROID_REPORT not_written errno=%d\n", errno); return; }
    FILE *stream = fdopen(out, "w");
    if (!stream) { printf("PW3_ANDROID_REPORT not_written errno=%d\n", errno); close(out); return; }
    unsigned kept, left_out;
    int bad = pw3_report_write(stream, rep.text, rep.bytes, rep.boot, &kept, &left_out) || fsync(out);
    if (fclose(stream) || fsync(output)) bad = 1;
    if (bad) {
        printf("PW3_ANDROID_REPORT incomplete errno=%d; removed\n", errno);
        unlinkat(output, ANDROID_REPORT_LOG, 0);
        return;
    }
    printf("PW3_ANDROID_REPORT boot=%u kept=%u left_out=%u\n", rep.boot, kept, left_out);
    /* And what these folders could not say before: whether anything ran between
     * the previous tap and this one.
     *
     * What the counter proves, exactly: it goes up when Android got as far as
     * pw3-boot-report and that program's write to the report area succeeded. It
     * is deliberately not boot_completed -- pw3-boot-report.rc starts on
     * sys.pw3.storage_ready because a boot that never completes is the boot
     * whose report is worth having -- so a greater counter is not proof that the
     * framework came up, and an unchanged counter is not proof that nothing ran:
     * a start that reached Android and then failed to write, or was cut off
     * before the write, leaves the number where it was.
     *
     * So the words here are what was observed and nothing more. `reported` is a
     * new report; `no_new_report` says which two readings agree and leaves the
     * reading of it to the two cases in docs/known-issues.md. The first version
     * of this printed `started` and `not_started`, which asserted both of the
     * things the counter cannot settle. */
    const char *word = pw3_logs_start_word(found, before, rep.boot);
    if (found > 0)
        printf("PW3_ANDROID_START %s previous_boot=%u this_boot=%u\n", word, before, rep.boot);
    else if (found == 0)
        printf("PW3_ANDROID_START %s this_boot=%u\n", word, rep.boot);
    else
        printf("PW3_ANDROID_START %s this_boot=%u errno=%d\n", word, rep.boot, errno);
}
#endif
#include "client-pm.inc"
static unsigned long allocation_parameter(const char *name) {
    char path[160],text[64],extra;unsigned long value;
    snprintf(path,sizeof(path),"/sys/module/pw3_first_kernel/parameters/allocation_failure_%s",name);
    require(read_pm(path,text,sizeof(text)) && sscanf(text,"%lu %c",&value,&extra)==1,"allocation_failure_parameter");
    return value;
}
static void allocation_memory_record(unsigned attempt) {
    const char *names[]={"meminfo","buddyinfo"};char path[80],filename[80],text[16384];
    for(unsigned i=0;i<2;i++) {
        snprintf(path,sizeof(path),"/proc/%s",names[i]);int fd=open(path,O_RDONLY|O_NOFOLLOW|O_CLOEXEC);
        require(fd>=0,"allocation_memory_open");ssize_t n=read(fd,text,sizeof(text)-1);int saved=errno;close(fd);errno=saved;
        require(n>0 && (size_t)n<sizeof(text)-1,"allocation_memory_read");text[n]=0;
        snprintf(filename,sizeof(filename),"allocation-%u-%s.txt",attempt,names[i]);write_result(filename,text);
    }
}
static void begin_with_retry(struct pws_begin *begin) {
    for(unsigned attempt=1;attempt<=3;attempt++) {
        checkpoint("before_allocation_attempt");
        if(ioctl(control,PWS_BEGIN,begin)==0)return;
        int saved=errno;require(saved==ENOMEM,"begin_owned_allocation");
        unsigned long reason=allocation_parameter("reason"),order=allocation_parameter("order");
        unsigned long accepted=allocation_parameter("accepted"),rejected=allocation_parameter("rejected");
        unsigned long limit=allocation_parameter("limit");
        struct pws_status s=status(PWS_EMPTY);
        require(!s.payload_pages && !s.control_pages && !s.collision_pages && live_pages()==0,"allocation_failure_fully_released");
        char filename[80],record[512];snprintf(filename,sizeof(filename),"allocation-%u-failure.txt",attempt);
        snprintf(record,sizeof(record),"schema=pw3-allocation-failure-v2\nattempt=%u\nerrno=%d\nreason=%lu\norder=%lu\naccepted_before_cleanup=%lu\nrejected_before_cleanup=%lu\nset_aside_limit=%lu\nowned_pages_after_cleanup=0\nmaximum_attempts=3\n",attempt,saved,reason,order,accepted,rejected,limit);
        write_result(filename,record);allocation_memory_record(attempt);
        printf("PW3_FIRST_KERNEL_ALLOCATION_RETRY attempt=%u reason=%lu order=%lu accepted=%lu rejected=%lu limit=%lu owned_pages=0\n",attempt,reason,order,accepted,rejected,limit);
        if(attempt==3){
            errno=saved;
            /* The one start failure the person holding the Kindle can do
             * something about: the stock system had no memory to spare for
             * the pages the jump needs, and a restart gives it back. Set
             * before require(), which shows the general screen otherwise. */
#ifdef PW3_INSTALLER
            if(!stopping){stopping=1;stop_shown=show(PW3_SCREEN_E403);}
#endif
            require(0,"begin_owned_allocation_after_three_attempts");
        }
        sleep(1);
    }
}
/* This release's system and data images on the user store (installer/install/),
 * before anything is loaded. Held for the rest of the run: the android folder's lock,
 * so a second tap cannot work on the same files. Exit status 3: the reason is on
 * the screen. */
#ifdef PW3_INSTALLER
static int install_lock = -1, install_upgraded;
static void open_screens(void) {
    snprintf(screen_dir, sizeof(screen_dir), "/tmp/pw3-screen-%ld", (long)getpid());
    if (!mkdir(screen_dir, 0700)) { screen_init(&screen, pw3_screens, screen_dir); screen_ready = 1; }
}
/* What this tap is allowed to touch, settled before it touches any of it: this
 * Kindle is the right one, and no other tap holds the android folder. Split out
 * of install() so that main() can call it before the stale-module cleanup,
 * which is the one step that reaches into what another tap may be in the middle
 * of (the comment at the call). */
static void install_prepare(void) {
    struct kindle k; struct inst_ops ops; struct inst_result r = {0};
    kindle_ops(&k, &screen, &ops);
    /* Which Kindle this is, before anything is downloaded or written. What puts
     * this file in the library is the jailbreak, not us, so it appears on any
     * model someone copies it to, and the device data that would have caught it
     * is only made at the handover -- by then 196 MB has been fetched and 2.3 GB
     * of images written on a device that cannot use them. Before the lock, so
     * that a Kindle this release cannot be installed on is told so rather than
     * having a lock file left on its user store. */
    struct dd_why why = {{0}, 0};
    if (dd_device_matches("/", &dd_pw3_5_16_2_1_1, &why)) {
        fprintf(stderr, "PW3_DEVICE_DATA %s\n", why.text);
        stop_now(why.other_device ? PW3_SCREEN_E101 : PW3_SCREEN_STOPPED);
    }
    install_lock = kindle_lock("/mnt/us");
    if (install_lock < 0) {
        r.code = errno == EWOULDBLOCK ? INST_E_RUNNING : INST_E_IO; r.sys_errno = errno;
        printf("PW3_INSTALL lock: %s\n", strerror(errno));
        if (!stopping) { stopping = 1; stop_shown = kindle_show_error(&k, &r); }
        exit(stop_shown ? 3 : 1);
    }
}
static void install(void) {
    struct kindle k; struct inst_ops ops; struct inst_result r = {0};
    kindle_ops(&k, &screen, &ops);
    char work[64]; snprintf(work, sizeof(work), "/tmp/pw3-install-%ld", (long)getpid());
    require(mkdir(work, 0700) == 0, "install_workspace");
    const struct inst_paths paths = {"/mnt/us", work};
    kindle_keep_awake(&k);
    enum inst_code code = inst_ensure(&pw3_release, &paths, &ops, &r);
    kindle_restore_awake(&k);
    rmdir(work);
    if (code) {
        if (!stopping) { stopping = 1; stop_shown = kindle_show_error(&k, &r); }
        exit(stop_shown ? 3 : 1);
    }
    install_upgraded = r.upgraded;
}
#endif
/* A computer on the USB cable: the stock kernel then does not suspend, because the
 * controller's wakeup interrupt is pending (check_wakeup_irqs; on the device, Test V40:
 * pm_suspend -16 with a Mac on the cable), so Android cannot be started. The attempt
 * would also make the computer see the Kindle reconnect, and the stock system's USB
 * screen would cover the reason. So it is asked first, before anything is changed:
 * "connected" is 1 once a computer has given the controller an address (arcotg_udc);
 * a charger leaves it 0. Exit status 3 when the reason is on the screen. */
static void no_computer_on_usb(void) {
    char text[8];
    if (!read_pm("/sys/devices/platform/fsl-usb2-udc/gadget/connected", text, sizeof(text)) || text[0] != '1') return;
    puts("PW3_FIRST_KERNEL_STOP computer_on_usb=1");
#ifdef PW3_INSTALLER
    stop_now(PW3_SCREEN_E104);
#else
    display("USB CABLE TO A COMPUTER. UNPLUG IT, TAP AGAIN.");
    exit(3);
#endif
}
int main(int argc, char **argv) {
    setvbuf(stdout, NULL, _IOLBF, 0); umask(077);
    /* The launcher's own last line (launcher-template.sh, finish): drawn when
     * this program could not show a screen of its own, and gone a second after
     * the script exits for the same reason as every other one. Only the hold,
     * nothing else: no folder, no module, no lock. A build that draws no
     * installer screens has nothing to hold and answers at once. */
    if (argc == 2 && !strcmp(argv[1], "--hold-screen")) {
#if defined(PW3_INSTALLER) && CHECK_PROFILE == 1
        signal(SIGTERM, notice); signal(SIGINT, notice); signal(SIGHUP, notice);
        kindle_hold_screen(&terminated);
#endif
        return 0;
    }
    require(atexit(cleanup) == 0, "cleanup_registration");
    signal(SIGALRM, notice); signal(SIGTERM, notice); signal(SIGINT, notice); signal(SIGHUP, notice); alarm(90);
    require(argc == 2 && getuid() == 0 && geteuid() == 0, "explicit_root_invocation");
    const char *prefix = PW3_OUTPUT_PREFIX;
    require(!strncmp(argv[1], prefix, strlen(prefix)), "output_prefix");
    const char *suffix = argv[1] + strlen(prefix); require(strlen(suffix) >= 2 && strlen(suffix) <= 80, "output_length");
    for (const char *p = suffix; *p; p++) require((*p >= '0' && *p <= '9') || *p == 'T' || *p == 'Z' || *p == '-', "output_characters");
    output = open(argv[1], O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC); require(output >= 0, "output_directory");
    /* This folder is held for as long as this program lives, so that another
     * tap's rotation leaves it alone (userlog.h). It is asked for here, as
     * early as the folder is open, because everything after this is work
     * another tap could be rotating through -- but nothing is decided on the
     * answer. The decision is made further down, once the install lock is
     * held: from there no other tap can rotate at all, so a folder that is
     * still ours there stays ours for the rest of the run, whether or not this
     * lock was given. Deciding here instead would stop a run over a rotation
     * that goes on to keep the folder anyway (it keeps one it cannot read, or
     * one whose rmdir fails), and that run would have been fine.
     *
     * The line is printed because a folder sent to a stranger should say what
     * was protecting it. A 1 says this store gives the lock; a 0 says only
     * that it was not given in five tries, which on this kernel can be a
     * refused allocation rather than anything about the store. */
    printf("PW3_LOGS_HOLD held=%d\n", pw3_logs_hold(output, argv[1]));
    /* The counter any earlier tap recorded is read before rotation, not after.
     * Rotation keeps the newest folders by name, and a clock that went back puts
     * the newest run under the smallest name -- so it can delete the very folder
     * whose counter the comparison needs, and the comparison would then find a
     * smaller one and call a report it has already seen a new one. */
#ifdef PW3_INSTALLER
    unsigned previous_boot = 0;
    const int previous_found = previous_report_boot(suffix, &previous_boot);
#endif
    save_previous_kernel_log();
#ifdef PW3_INSTALLER
    save_android_report(previous_found, previous_boot);
#endif
    struct utsname u; require(uname(&u) == 0, "uname");
#if CHECK_PROFILE == 1
    /* The display before the kernel it belongs to: every screen this program can
     * show goes through /usr/sbin/eips, so its identity is what makes a screen
     * trustworthy, and it is checked first. Nothing can be drawn when it fails,
     * and the launcher's own fallback line checks the same hash and stays quiet
     * too, so this one exits 1 -- 3 would tell the launcher a reason is on the
     * screen when none is. */
    if (!exact_file("/usr/sbin/eips", "73eb0d2532f9c899e98fb8feacb7a085ab0652f628f1c2c7b2e2d1cefae3f4ae", 62176)) {
        fprintf(stderr, "PW3_FIRST_KERNEL_CHECK_FAIL check=display_identity errno=%d checks=%u\n", errno, ++checks);
        exit(1);
    }
#endif
    /* Opened here, before the first check that can stop a tap for a reason the
     * person has to be told: the kernel below. Opening it after meant that a
     * Kindle of another model, or the same model on another firmware, took the
     * stock_profile check, showed nothing at all (screen_ready was still 0) and
     * exited 3, which the launcher reads as "the reason is on the screen" -- so
     * the one case this project knows a stranger will hit, and has an E101
     * screen for, was the one case that said nothing. */
#ifdef PW3_INSTALLER
    open_screens();
#endif
#if CHECK_PROFILE == 1
    if (strcmp(u.release, "3.0.35-lab126") || strcmp(u.version, "#8 PREEMPT Tue Aug 1 12:49:59 UTC 2023") ||
        strcmp(u.machine, "armv7l")) {
        fprintf(stderr, "PW3_FIRST_KERNEL_CHECK_FAIL check=stock_profile errno=%d checks=%u\n", errno, ++checks);
        /* Not this Kindle, or not this firmware: the same answer the device data
         * gives for it (device_data_failed), and for the same reason -- what put
         * this file in their library is the jailbreak, not us. */
#ifdef PW3_INSTALLER
        stop_now(PW3_SCREEN_E101);
#endif
        exit(1);
    }
#else
    (void)exact_file; require(strstr(u.release, "-pw3-core-smoke") != NULL, "virtual_profile");
#endif
    /* The stock system's own files are what this program must leave alone, and
     * exact_file() is what says so. Whether "/" is mounted read-only is the
     * jailbreak's state, not something a tap can require: the hotfix that puts
     * this entry in the library writes /etc and /usr/bin, and on 5.16.2.1.1
     * that cannot be undone from the running system -- `mntroot ro` answers
     * "mount: / is busy" -- so requiring ro refused exactly the devices this
     * entry needs a jailbreak to reach. 2026-11-06: a PW3 on 5.16.2.1.1 with
     * LanguageBreak and the MKK hotfix stopped here on every tap and wrote
     * nothing, with original_boot_verified=1 and root_readonly_verified=0.
     *
     * What ro stood in for is that these files cannot change between the check
     * and the handoff, and that is checked where it matters: original_boot()
     * runs again after the probe, immediately before the commit, so the files
     * are the original ones at the moment the kernel is started. A writable
     * root is reported rather than refused -- PW3_FIRST_KERNEL_CLEANUP carries
     * root_readonly_verified and preflight-complete.txt carries
     * root_readonly=0 -- because it says what the device was like, not what
     * went wrong with the tap. */
    require(original_boot(), "original_boot_before_probe");
    /* Which Kindle this is, and then the android folder's lock, before the
     * cleanup below reaches into something another tap may own. Until
     * 2026-10-27 the lock was taken inside install(), four steps further on,
     * and the delete_module() below ran outside it: the reference the control
     * file holds on the module begins at the open and not at init_module(), so
     * a second tap arriving in the window between those two unloaded the module
     * the first had just loaded, and the first then failed at the misc device
     * or at the control open. The kernel's own refusal covers a running
     * instance; it does not cover a starting one, and the lock covers both. */
#ifdef PW3_INSTALLER
    install_prepare();
#endif
    /* Now that no other tap can rotate, the one place where this folder's
     * being ours can be settled rather than hoped for. Before the lock it
     * could not be: a tap that was not given the shared lock -- this kernel
     * allocates a lock before it looks for a conflicting one, and that
     * allocation can fail -- had nothing holding its folder, and a rotation
     * could take it between the asking and here. After the lock, nothing can,
     * so an answer here holds for the rest of the run.
     *
     * Stopping is what is owed to the reader: a folder that is gone takes
     * every file this run has to write with it, one at a time, each failing
     * somewhere that says nothing about why. The next tap makes a new folder
     * and is not in this position, so nothing is lost by stopping. */
    require(pw3_logs_hold(output, argv[1]) >= 0, "output_directory_gone");
    /* And rotation under that same lock. A drive that holds someone's books does
     * not gain one folder per tap for ever, so a tap keeps the newest few and
     * deletes the rest -- but a folder another tap is still writing is not this
     * one's to delete, and until 2026-10-27 this ran before the lock. Five taps
     * during one long install were enough: each rotated, and the fifth pushed
     * the installing tap's own folder out of the kept set, took the folder with
     * its files, and the next write_result() there failed on a directory that no
     * longer had a name. No clock going backwards was needed, and what was lost
     * was not only the diagnostics.
     *
     * Under the lock only one tap rotates, and rotation never deletes the folder
     * of the tap doing it. A tap that cannot have the lock exits without
     * rotating, so its folders simply wait for whoever holds it next. The
     * stretch before the lock is covered by two other things and not by the
     * order: the shared lock each run takes on its own folder, which stops a
     * rotation removing it, and the check above, which settles here -- where
     * no rotation can run -- whether this folder survived that stretch at all.
     * The count is its own line in the log because a report with five folders
     * should say so. */
#ifdef PW3_INSTALLER
    printf("PW3_LOGS removed=%d kept=%d\n", pw3_logs_rotate(PW3_LOG_DIR, suffix, PW3_LOGS_KEPT), PW3_LOGS_KEPT);
#endif
    /* A module left behind by a start that was killed outright: the stock system
     * runs short of memory, the OOM killer takes this program, and the atexit
     * cleanup that would have unloaded the module never runs. Nothing is wrong
     * with the module -- it is loaded with nobody holding it -- but refusing
     * every later tap over it leaves the owner one way out, a restart they have
     * no reason to know they need. So it is unloaded once and the tap goes on.
     *
     * Whether that is safe is the kernel's judgement rather than ours: the
     * control file holds a reference to the module while it is open, so this
     * fails against an instance that is still running, and the check below then
     * refuses exactly as it did before. */
    if (present() == 1 && !syscall(SYS_delete_module, "pw3_first_kernel", O_NONBLOCK))
        puts("PW3_FIRST_KERNEL_STALE_MODULE unloaded=1");
    require(present() == 0, "no_existing_stage_module");
    no_computer_on_usb();
#ifdef PW3_INSTALLER
    alarm(0); install(); alarm(90);
#endif
    preflight_pm();
    unsigned char actual[32]; digest(module_payload, MODULE_BYTES, actual);
    require(!memcmp(actual, module_sha256, sizeof(actual)), "module_payload_digest");
    digest(kernel_payload, KERNEL_BYTES, actual); require(!memcmp(actual, kernel_sha256, 32), "kernel_digest");
    digest(public_initramfs_payload, PUBLIC_INITRAMFS_BYTES, actual); require(!memcmp(actual, public_initramfs_sha256, 32), "public_initramfs_digest");
    /* What only this device has, from the running stock system: the archive
     * appended to the public initramfs (after zero padding to four bytes),
     * then the ATAGs that name the whole initramfs. */
    static const struct dd_build build = {BUILD_CMDLINE, BUILD_PREINIT_CONF, BUILD_DATA_PATH, BUILD_DATA_SIZE};
    struct dd_buf archive = {0}, atags = {0}; struct dd_why why = {{0}, 0};
    if (dd_archive("/", &dd_pw3_5_16_2_1_1, &build, &archive, &why)) { device_data_failed(&why, "device_archive"); }
    static const unsigned char zeros[4];
    const uint32_t padding = (4u - PUBLIC_INITRAMFS_BYTES % 4u) % 4u;
    require(archive.size <= 16u << 20, "device_archive_size");
    const uint32_t initramfs_bytes = PUBLIC_INITRAMFS_BYTES + padding + (uint32_t)archive.size;
    if (dd_atags("/", &dd_pw3_5_16_2_1_1, BUILD_CMDLINE, INITRD_START, initramfs_bytes, &atags, &why)) { device_data_failed(&why, "device_atags"); }
    const struct piece slots[PWS_SLOTS][3] = {
        {{kernel_payload, KERNEL_BYTES}},
        {{atags.data, (uint32_t)atags.size}},
        {{public_initramfs_payload, PUBLIC_INITRAMFS_BYTES}, {zeros, padding}, {archive.data, (uint32_t)archive.size}},
    };
    uint32_t slot_bytes[PWS_SLOTS];
    struct pws_begin begin = {.version = PWS_VERSION};
    for (unsigned i = 0; i < PWS_SLOTS; i++) {
        SHA256_CTX ctx; sha256_init(&ctx); slot_bytes[i] = 0;
        for (unsigned k = 0; k < 3; k++) { sha256_update(&ctx, slots[i][k].data, slots[i][k].bytes); slot_bytes[i] += slots[i][k].bytes; }
        sha256_final(&ctx, begin.images[i].sha256); begin.images[i].bytes = slot_bytes[i];
    }
    printf("PW3_DEVICE_DATA atags=%u archive=%u initramfs=%u\n", (unsigned)atags.size, (unsigned)archive.size, (unsigned)initramfs_bytes);
    checkpoint("before_load");
#if defined(PW3_INSTALLER)
    show(PW3_SCREEN_PREPARE);
#elif defined(PW3_ANDROID_FIRST_BOOT)
    display("ANDROID PREPARING. PLEASE WAIT.");
#else
    display("FIRST KERNEL CHECK. PLEASE WAIT.");
#endif
    snprintf(workspace, sizeof(workspace), "/tmp/pw3-first-kernel-%ld", (long)getpid());
    require(mkdir(workspace, 0700) == 0, "new_private_workspace"); workspace_created = 1;
    require(syscall(SYS_init_module, module_payload, (size_t)MODULE_BYTES, "") == 0, "module_load"); loaded = 1;
    FILE *stream = fopen("/proc/misc", "r"); require(stream != NULL, "misc_listing");
    unsigned number = 0, candidate, seen = 0; char name[128], line[256];
    while (fgets(line, sizeof(line), stream)) if (sscanf(line, "%u %127s", &candidate, name) == 2 && !strcmp(name, "pw3-first-kernel")) { number = candidate; seen++; }
    require(!ferror(stream), "misc_listing_read"); fclose(stream); require(seen == 1 && number < 255, "unique_misc_device");
    snprintf(node, sizeof(node), "%s/control", workspace);
    require(mknod(node, S_IFCHR | 0600, makedev(10, number)) == 0, "private_control_node");
    control = open(node, O_RDWR | O_NOFOLLOW | O_CLOEXEC); require(control >= 0, "open_control");
    struct stat st; require(fstat(control, &st) == 0 && S_ISCHR(st.st_mode) && st.st_uid == 0 && (st.st_mode & 0777) == 0600 && st.st_rdev == makedev(10, number), "control_identity");
    struct pws_status s = status(PWS_EMPTY); require(!s.payload_pages && !s.control_pages && live_pages() == 0, "empty_initial_state");
    begin_with_retry(&begin);
    s = status(PWS_WRITING); report("allocated", &s); checkpoint("after_begin");
    for (unsigned i = 0; i < PWS_SLOTS; i++) for (unsigned k = 0, off = 0; k < 3; k++) for (uint32_t at = 0; at < slots[i][k].bytes;) {
        uint32_t bytes = slots[i][k].bytes - at; if (bytes > 65536) bytes = 65536;
        struct pws_put put = {.slot = i, .offset = off, .bytes = bytes, .user_buffer = (uintptr_t)(slots[i][k].data + at)};
        at += bytes;
        require(ioctl(control, PWS_PUT, &put) == 0, "bounded_component_copy"); off += bytes; checkpoint("during_copy");
    }
    require(ioctl(control, PWS_SEAL, 0) == 0, "seal_owned_snapshot"); s = status(PWS_SEALED);
    for (unsigned i = 0; i < PWS_SLOTS; i++) require(s.written[i] == slot_bytes[i] && s.sizes[i] == slot_bytes[i], "sealed_sizes");
    report("sealed", &s); checkpoint("after_seal");
    require(ioctl(control, PWS_PREPARE, 0) == 0, "prepare_inactive_copy_plan"); s = status(PWS_PREPARED); report("prepared", &s);
    struct pws_plan_status plan = {0}; require(ioctl(control, PWS_PLAN_STATUS, &plan) == 0, "plan_status");
    require(plan.version == PWS_VERSION && plan.state == PWS_PREPARED && plan.copy_plan_verified == 1 && plan.source_pages == s.payload_pages && plan.list_pages > 0 && plan.pgd_entries == 4096 && plan.boot_footprint_verified==1 && plan.execute_available==1, "pinned_kernel_plan_contract");
    require(live_pages() == s.payload_pages + s.control_pages + s.collision_pages, "live_allocation_accounting");
    checkpoint("after_prepare");
    require(mlockall(MCL_CURRENT|MCL_FUTURE)==0,"lock_client_memory");
    sleep(1);run_native_cycle(0);
    /* The same check as before the probe, and the one that carries the weight
     * the read-only root used to carry: this is the last look at the stock
     * files before the kernel is started. */
    require(original_boot(),"original_boot_after_probe");
    char preflight[256];
    snprintf(preflight, sizeof preflight,
        "schema=pw3-first-kernel-preflight-v1\ncore_roundtrip_and_hardware_guard=1\n"
        "original_boot_verified=1\nroot_readonly=%d\nnew_kernel_attempted=0\n", root_readonly());
    write_result("preflight-complete.txt", preflight);
    checkpoint("before_commit");
#if defined(PW3_INSTALLER)
    show(install_upgraded ? PW3_SCREEN_BOOT_UPGRADE : PW3_SCREEN_BOOT);
#elif defined(PW3_ANDROID_FIRST_BOOT)
    display("ANDROID BOOT 3 MIN. IF STUCK HOLD POWER 20S.");
#else
    display("BOOT ATTEMPT. WAIT 30S THEN USB.");
#endif
    sleep(2);sync();
    /* The screen, the two seconds and the sync are all after the last look at
     * the cancel flag, and a signal that arrives in them ends the sleep early,
     * so without this the switch would happen sooner for having been asked to
     * stop. Everything before it is still undone by a restart. */
    checkpoint("before_commit_cycle");
    run_native_cycle(1);
    require(0,"new_kernel_commit_returned");return 1;
}
