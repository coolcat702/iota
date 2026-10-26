/* runtime for compiled Iota programs.
 *
 * Strings cross the ABI as arrays of 32-bit code points (Char = i32), never
 * as Iota lists: the generated code owns list layout, this file owns I/O.
 * Every buffer returned here was allocated with malloc; the generated code
 * releases it with rt_free.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <inttypes.h>
#include <signal.h>
#include <ucontext.h>
#include <sys/mman.h>
#include <unistd.h>
#include <time.h>
#include <sys/resource.h>
#include <errno.h>
#include <fcntl.h>
#include <dirent.h>
#include <poll.h>
#include <termios.h>
#include <sys/ioctl.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <math.h>

/* The generated code stores a constructor tag in the low bits of heap pointers, so
 * every object must be 16-byte aligned (malloc guarantees alignof(max_align_t)). */
static uint64_t st_allocs, st_bytes, st_frees, st_live, st_peak;
static struct timespec st_start;

void *rt_alloc(uint64_t n) {
	void *p = malloc(n ? n : 16);
	if (!p) {
		fputs("iota: out of memory\n", stderr);
		exit(101);
	}
	st_allocs++;
	st_bytes += n;
	if (++st_live > st_peak) st_peak = st_live;
	return p;
}
void rt_free(void *p) {
	st_frees++;
	st_live--;
	free(p);
}

uint32_t *rt_buf_alloc(uint64_t n) {
	return (uint32_t *)rt_alloc((n ? n : 1) * sizeof(uint32_t));
}

/* Abort with a runtime error: `extern`, a failed pattern match, ... */
void rt_fail(const char *msg) {
	fflush(stdout);
	fprintf(stderr, "iota: runtime error: %s\n", msg);
	exit(102);
}

/* div, mod are Euclidean
 * This matches the constant folder in optimize.rs, so
 * a folded and an unfolded computation can never disagree. */
int32_t rt_idiv(int32_t a, int32_t b) {
	if (b == 0) return 0;
	if (b == -1) return (int32_t)(0u - (uint32_t)a); /* avoids INT_MIN / -1 trap */
	int q = a / b;
	int r = a % b;
	if (r < 0) q += (b < 0) ? 1 : -1;
	return q;
}
int32_t rt_imod(int32_t a, int32_t b) {
	if (b == 0) return 0;
	if (b == -1) return 0;
	int32_t r = a % b;
	if (r < 0) r += (b < 0 ? -b : b);
	return r;
}

static uint32_t *from_ascii(const char *s, uint64_t *len) {
	uint64_t n = strlen(s);
	uint32_t *b = rt_buf_alloc(n);
	for (uint64_t i = 0; i < n; i++) b[i] = (unsigned char)s[i];
	*len = n;
	return b;
}
uint32_t *rt_show_int(int32_t v, uint64_t *len) {
	char tmp[32];
	snprintf(tmp, sizeof tmp, "%" PRId32, v);
	return from_ascii(tmp, len);
}
uint32_t *rt_show_float(double v, uint64_t *len) {
	char tmp[64];
	snprintf(tmp, sizeof tmp, "%g", v);
	return from_ascii(tmp, len);
}

/* The shortest decimal text that reads back as exactly this double (so, unlike `%g`,
 * nothing is lost). Whole numbers below 1e15 print without an exponent. */
uint32_t *rt_float_repr(double v, uint64_t *len) {
	char tmp[64];
	if (v != v) snprintf(tmp, sizeof tmp, "nan");
	else if (v > 1.7976931348623157e308 || v < -1.7976931348623157e308) snprintf(tmp, sizeof tmp, v > 0 ? "inf" : "-inf");
	else if (v == (double)(long long)v && v > -1e15 && v < 1e15) snprintf(tmp, sizeof tmp, "%lld", (long long)v);
	else {
		for (int prec = 1; prec <= 17; prec++) {
			snprintf(tmp, sizeof tmp, "%.*g", prec, v);
			if (strtod(tmp, NULL) == v) break;
		}
	}
	return from_ascii(tmp, len);
}

static void put_utf8(uint32_t c) {
	if (c < 0x80) putchar((int)c);
	else if (c < 0x800) {
		putchar(0xC0 | (c >> 6));
		putchar(0x80 | (c & 0x3F));
	}
	else if (c < 0x10000) {
		putchar(0xE0 | (c >> 12));
		putchar(0x80 | ((c >> 6) & 0x3F));
		putchar(0x80 | (c & 0x3F));
	}
	else {
		putchar(0xF0 | (c >> 18));
		putchar(0x80 | ((c >> 12) & 0x3F));
		putchar(0x80 | ((c >> 6) & 0x3F));
		putchar(0x80 | (c & 0x3F));
	}
}

/* A string is a lazy list, so printing one forces it cell by cell; the generated
 * code appends each character to a builder and prints once the list is complete
 * (so an error while evaluating the tail prints nothing instead of half a line). */
typedef struct {
	uint32_t *data;
	uint64_t len, cap;
} StrBuf;

StrBuf *rt_sb_new(void) {
	StrBuf *b = (StrBuf *)rt_alloc(sizeof(StrBuf));
	b->cap = 64;
	b->len = 0;
	b->data = (uint32_t *)rt_alloc(b->cap * sizeof(uint32_t));
	return b;
}
void rt_sb_push(StrBuf *b, uint32_t c) {
	if (b->len == b->cap) {
		b->cap *= 2;
		b->data = (uint32_t *)realloc(b->data, b->cap * sizeof(uint32_t));
		if (!b->data) {
			fputs("iota: out of memory\n", stderr);
			exit(101);
		}
	}
	b->data[b->len++] = c;
}
void rt_print_sb(StrBuf *b, int32_t newline) {
	for (uint64_t i = 0; i < b->len; i++) put_utf8(b->data[i]);
	if (newline) putchar('\n');
	rt_free(b->data);
	rt_free(b);
}

/* ------------------------------------------------------------------------- *
 * UTF-8 and the string ABI
 *
 * Strings cross the ABI as arrays of 32-bit code points. Fallible primitives return
 * a "status string": element 0 is a status code (0 = success), the rest is the payload
 * (or, on failure, the error message). std/io.iota decodes it into an `Either`.
 * ------------------------------------------------------------------------- */

/* Lenient decoder: a malformed byte becomes U+FFFD and decoding resynchronises on the
 * next byte. `out` needs room for `n` code points. Returns how many were written. */
static uint64_t utf8_decode(const unsigned char *s, size_t n, uint32_t *out) {
	uint64_t m = 0;
	for (size_t i = 0; i < n;) {
		unsigned char b = s[i];
		uint32_t cp;
		int extra;
		if (b < 0x80) {
			cp = b;
			extra = 0;
		}
		else if ((b >> 5) == 6) {
			cp = b & 0x1F;
			extra = 1;
		}
		else if ((b >> 4) == 14) {
			cp = b & 0x0F;
			extra = 2;
		}
		else if ((b >> 3) == 30) {
			cp = b & 0x07;
			extra = 3;
		}
		else {
			out[m++] = 0xFFFD;
			i++;
			continue;
		}
		i++;
		int ok = 1;
		for (int k = 0; k < extra; k++) {
			if (i >= n || (s[i] & 0xC0) != 0x80) {
				ok = 0;
				break;
			}
			cp = (cp << 6) | (s[i] & 0x3F);
			i++;
		}
		out[m++] = ok ? cp : 0xFFFD;
	}
	return m;
}

/* Encodes one code point; returns the number of bytes written (1..4). */
static size_t utf8_encode(uint32_t c, unsigned char *o) {
	if (c > 0x10FFFF || (c >= 0xD800 && c <= 0xDFFF)) c = 0xFFFD;
	if (c < 0x80) {
		o[0] = (unsigned char)c;
		return 1;
	}
	if (c < 0x800) {
		o[0] = (unsigned char)(0xC0 | (c >> 6));
		o[1] = (unsigned char)(0x80 | (c & 0x3F));
		return 2;
	}
	if (c < 0x10000) {
		o[0] = (unsigned char)(0xE0 | (c >> 12));
		o[1] = (unsigned char)(0x80 | ((c >> 6) & 0x3F));
		o[2] = (unsigned char)(0x80 | (c & 0x3F));
		return 3;
	}
	o[0] = (unsigned char)(0xF0 | (c >> 18));
	o[1] = (unsigned char)(0x80 | ((c >> 12) & 0x3F));
	o[2] = (unsigned char)(0x80 | ((c >> 6) & 0x3F));
	o[3] = (unsigned char)(0x80 | (c & 0x3F));
	return 4;
}

static void sb_release(StrBuf *b) {
	rt_free(b->data);
	rt_free(b);
}

/* Turns an Iota string into bytes and releases it. `bytes_mode`: each code point is one
 * byte (its low 8 bits) instead of being UTF-8 encoded. The result is malloc'd and
 * NUL-terminated (the NUL is not counted in *n); the caller frees it with free(). */
static char *sb_take(StrBuf *b, size_t *n, int bytes_mode) {
	char *out = (char *)malloc(b->len * 4 + 1);
	if (!out) {
		fputs("iota: out of memory\n", stderr);
		exit(101);
	}
	size_t m = 0;
	for (uint64_t i = 0; i < b->len; i++) {
		if (bytes_mode) out[m++] = (char)(b->data[i] & 0xFF);
		else m += utf8_encode(b->data[i], (unsigned char *)out + m);
	}
	out[m] = 0;
	if (n) *n = m;
	sb_release(b);
	return out;
}
static char *sb_cstr(StrBuf *b) {
	return sb_take(b, NULL, 0);
}

/* [status][UTF-8 payload decoded]; or, with bytes_mode, one code point per byte */
static uint32_t *status_bytes(int32_t status, const unsigned char *payload, size_t n, int bytes_mode, uint64_t *len) {
	uint32_t *out = rt_buf_alloc(n + 1);
	out[0] = (uint32_t)status;
	uint64_t m = 0;
	if (bytes_mode) {
		for (size_t i = 0; i < n; i++) out[1 + i] = payload[i];
		m = n;
	}
	else m = utf8_decode(payload, n, out + 1);
	*len = 1 + m;
	return out;
}
static uint32_t *status_ok(const char *payload, uint64_t *len) {
	return status_bytes(0, (const unsigned char *)payload, strlen(payload), 0, len);
}
static uint32_t *status_empty(uint64_t *len) {
	uint32_t *out = rt_buf_alloc(1);
	out[0] = 0;
	*len = 1;
	return out;
}

/* error kinds; keep in sync with `IOError` in std/io.iota */
enum { E_OK = 0, E_NOT_FOUND = 1, E_PERMISSION = 2, E_EXISTS = 3, E_IS_DIR = 4, E_NOT_DIR = 5,
       E_NOT_EMPTY = 6, E_INVALID = 7, E_OTHER = 8, E_UNEXPECTED_EOF = 9 };

static int err_kind(int e) {
	switch (e) {
	case ENOENT: return E_NOT_FOUND;
	case EACCES: case EPERM: case EROFS: return E_PERMISSION;
	case EEXIST: return E_EXISTS;
	case EISDIR: return E_IS_DIR;
	case ENOTDIR: return E_NOT_DIR;
	case ENOTEMPTY: return E_NOT_EMPTY;
	case EINVAL: case ENAMETOOLONG: case ELOOP: return E_INVALID;
	default: return E_OTHER;
	}
}
static uint32_t *status_errno(int e, uint64_t *len) {
	const char *m = strerror(e);
	return status_bytes(err_kind(e), (const unsigned char *)m, strlen(m), 0, len);
}
static uint32_t *status_msg(int kind, const char *msg, uint64_t *len) {
	return status_bytes(kind, (const unsigned char *)msg, strlen(msg), 0, len);
}

int32_t rt_ftoi(double d) {
	if (d != d) return 0;
	if (d >= 2147483647.0) return INT32_MAX;
	if (d <= -2147483648.0) return INT32_MIN;
	return (int32_t)d;
}

/* ------------------------------------------------------------------------- *
 * Standard input
 *
 * One buffer feeds getln, the "read everything" and "optional line" primitives and
 * keypress input, so mixing them never loses bytes.
 * ------------------------------------------------------------------------- */

static unsigned char in_buf[4096];
static size_t in_pos, in_len;
static volatile sig_atomic_t winch_flag;
static int term_inited;

/* >0: bytes are buffered; 0: end of input; -1: timed out; -2: interrupted by SIGWINCH
 * (only when `report_resize`; otherwise a resize is ignored and the flag is left set for
 * `rt_term_resized`). timeout_ms < 0 waits forever. */
static int in_fill(int timeout_ms, int report_resize) {
	if (in_pos < in_len) return 1;
	for (;;) {
		if (timeout_ms >= 0 || term_inited) {
			struct pollfd p = {0, POLLIN, 0};
			int r = poll(&p, 1, timeout_ms);
			if (r < 0) {
				if (errno == EINTR) {
					if (winch_flag && report_resize) return -2;
					continue;
				}
				return 0;
			}
			if (r == 0) return -1;
		}
		ssize_t n = read(0, in_buf, sizeof in_buf);
		if (n < 0) {
			if (errno == EINTR) {
				if (winch_flag && report_resize) return -2;
				continue;
			}
			return 0;
		}
		if (n == 0) return 0;
		in_pos = 0;
		in_len = (size_t)n;
		return 1;
	}
}
/* next byte, or -1 on end of input */
static int in_getc(void) {
	int r = in_fill(-1, 0);
	if (r <= 0) return -1;
	return in_buf[in_pos++];
}

/* One line (no newline, and no trailing '\r') into a malloc'd byte buffer.
 * Returns 0 when the input ended before any byte was read. */
static int read_line_bytes(unsigned char **out, size_t *n) {
	size_t cap = 128, m = 0;
	unsigned char *line = (unsigned char *)malloc(cap);
	int c, any = 0;
	while ((c = in_getc()) != -1) {
		any = 1;
		if (c == '\n') break;
		if (m == cap) {
			cap *= 2;
			line = (unsigned char *)realloc(line, cap);
			if (!line) exit(101);
		}
		line[m++] = (unsigned char)c;
	}
	if (m && line[m - 1] == '\r') m--;
	*out = line;
	*n = m;
	return any;
}

/* One line from stdin without the newline.
 * On EOF with no input, returns the empty string. */
uint32_t *rt_getln(uint64_t *len) {
	fflush(stdout);
	unsigned char *line;
	size_t n;
	read_line_bytes(&line, &n);
	uint32_t *out = rt_buf_alloc(n);
	*len = utf8_decode(line, n, out);
	free(line);
	return out;
}

/* status 0 + a line, or status 1 at the end of the input */
uint32_t *rt_io_getln_opt(uint64_t *len) {
	fflush(stdout);
	unsigned char *line;
	size_t n;
	int any = read_line_bytes(&line, &n);
	uint32_t *r = any ? status_bytes(0, line, n, 0, len) : status_msg(1, "end of input", len);
	free(line);
	return r;
}

uint32_t *rt_io_stdin_all(uint64_t *len) {
	fflush(stdout);
	size_t cap = 4096, n = 0;
	unsigned char *buf = (unsigned char *)malloc(cap);
	int c;
	while ((c = in_getc()) != -1) {
		if (n == cap) {
			cap *= 2;
			buf = (unsigned char *)realloc(buf, cap);
			if (!buf) exit(101);
		}
		buf[n++] = (unsigned char)c;
	}
	uint32_t *out = rt_buf_alloc(n);
	*len = utf8_decode(buf, n, out);
	free(buf);
	return out;
}

void rt_io_flush(void) {
	fflush(stdout);
}

void rt_io_eprint(StrBuf *b, int32_t newline) {
	size_t n;
	char *s = sb_take(b, &n, 0);
	fflush(stdout);
	size_t off = 0;
	while (off < n) {
		ssize_t w = write(2, s + off, n - off);
		if (w < 0) {
			if (errno == EINTR) continue;
			break;
		}
		off += (size_t)w;
	}
	if (newline) {
		ssize_t w = write(2, "\n", 1);
		(void)w;
	}
	free(s);
}

/* ------------------------------------------------------------------------- *
 * The process and its environment
 * ------------------------------------------------------------------------- */

static int g_argc;
static char **g_argv;
extern char **environ;

static uint32_t *join_cstrs(char *const *v, int skip, uint64_t *len) {
	size_t total = 0;
	for (int i = skip; v && v[i]; i++) total += strlen(v[i]) + 1;
	unsigned char *buf = (unsigned char *)malloc(total ? total : 1);
	size_t o = 0;
	for (int i = skip; v && v[i]; i++) {
		size_t l = strlen(v[i]) + 1; /* includes the terminator */
		memcpy(buf + o, v[i], l);
		o += l;
	}
	uint32_t *out = rt_buf_alloc(total);
	*len = utf8_decode(buf, total, out);
	free(buf);
	return out;
}

/* every argument (the program name excluded), each followed by a NUL */
uint32_t *rt_sys_args(uint64_t *len) {
	return join_cstrs(g_argv, 1, len);
}
uint32_t *rt_sys_environ(uint64_t *len) {
	return join_cstrs(environ, 0, len);
}
uint32_t *rt_sys_getenv(StrBuf *name, uint64_t *len) {
	char *n = sb_cstr(name);
	const char *v = getenv(n);
	free(n);
	return v ? status_ok(v, len) : status_msg(1, "not set", len);
}
int32_t rt_sys_pid(void) {
	return (int32_t)getpid();
}

static void term_restore(void);
void rt_sys_exit(int32_t code) {
	fflush(stdout);
	term_restore();
	exit((int)code);
}

/* ------------------------------------------------------------------------- *
 * File system
 * ------------------------------------------------------------------------- */

static uint32_t *do_read(const char *path, int bytes_mode, uint64_t *len) {
	int fd = open(path, O_RDONLY);
	if (fd < 0) return status_errno(errno, len);
	struct stat st;
	if (fstat(fd, &st) == 0 && S_ISDIR(st.st_mode)) {
		close(fd);
		return status_errno(EISDIR, len);
	}
	size_t cap = st.st_size > 0 ? (size_t)st.st_size + 1 : 4096, n = 0;
	unsigned char *buf = (unsigned char *)malloc(cap);
	for (;;) {
		if (n == cap) {
			cap *= 2;
			buf = (unsigned char *)realloc(buf, cap);
			if (!buf) exit(101);
		}
		ssize_t r = read(fd, buf + n, cap - n);
		if (r < 0) {
			if (errno == EINTR) continue;
			int e = errno;
			free(buf);
			close(fd);
			return status_errno(e, len);
		}
		if (r == 0) break;
		n += (size_t)r;
	}
	close(fd);
	uint32_t *out = status_bytes(0, buf, n, bytes_mode, len);
	free(buf);
	return out;
}

/* mode: bit 0 = bytes, bit 1 = append */
uint32_t *rt_fs_read(StrBuf *path, int32_t mode, uint64_t *len) {
	char *p = sb_cstr(path);
	uint32_t *r = do_read(p, mode & 1, len);
	free(p);
	return r;
}

uint32_t *rt_fs_write(StrBuf *path, StrBuf *data, int32_t mode, uint64_t *len) {
	char *p = sb_cstr(path);
	size_t n;
	char *d = sb_take(data, &n, mode & 1);
	int flags = O_WRONLY | O_CREAT | ((mode & 2) ? O_APPEND : O_TRUNC);
	int fd = open(p, flags, 0666);
	uint32_t *r;
	if (fd < 0) {
		r = status_errno(errno, len);
	}
	else {
		size_t off = 0;
		int e = 0;
		while (off < n) {
			ssize_t w = write(fd, d + off, n - off);
			if (w < 0) {
				if (errno == EINTR) continue;
				e = errno;
				break;
			}
			off += (size_t)w;
		}
		if (close(fd) != 0 && !e) e = errno;
		r = e ? status_errno(e, len) : status_empty(len);
	}
	free(p);
	free(d);
	return r;
}

int32_t rt_fs_kind(StrBuf *path) {
	char *p = sb_cstr(path);
	struct stat st;
	int r = 0;
	if (stat(p, &st) == 0) r = S_ISREG(st.st_mode) ? 1 : S_ISDIR(st.st_mode) ? 2 : 3;
	free(p);
	return r;
}

/* "<kind> <size> <mtime seconds>" */
uint32_t *rt_fs_stat(StrBuf *path, uint64_t *len) {
	char *p = sb_cstr(path);
	struct stat st;
	uint32_t *r;
	if (stat(p, &st) != 0) {
		r = status_errno(errno, len);
	}
	else {
		char tmp[96];
		int kind = S_ISREG(st.st_mode) ? 1 : S_ISDIR(st.st_mode) ? 2 : 3;
		snprintf(tmp, sizeof tmp, "%d %lld %lld", kind, (long long)st.st_size, (long long)st.st_mtime);
		r = status_ok(tmp, len);
	}
	free(p);
	return r;
}

#define PATH_OP(name, expr)                                  \
	uint32_t *name(StrBuf *path, uint64_t *len) {             \
		char *p = sb_cstr(path);                              \
		int rc = (expr);                                      \
		int e = errno;                                        \
		free(p);                                              \
		return rc == 0 ? status_empty(len) : status_errno(e, len); \
	}
PATH_OP(rt_fs_remove, remove(p))
PATH_OP(rt_fs_mkdir, mkdir(p, 0777))
PATH_OP(rt_fs_chdir, chdir(p))

uint32_t *rt_fs_rename(StrBuf *from, StrBuf *to, uint64_t *len) {
	char *a = sb_cstr(from);
	char *b = sb_cstr(to);
	int rc = rename(a, b);
	int e = errno;
	free(a);
	free(b);
	return rc == 0 ? status_empty(len) : status_errno(e, len);
}

uint32_t *rt_fs_cwd(uint64_t *len) {
	char *buf = getcwd(NULL, 0);
	if (!buf) return status_errno(errno, len);
	uint32_t *r = status_ok(buf, len);
	free(buf);
	return r;
}

uint32_t *rt_fs_realpath(StrBuf *path, uint64_t *len) {
	char *p = sb_cstr(path);
	char *res = realpath(p, NULL);
	int e = errno;
	free(p);
	if (!res) return status_errno(e, len);
	uint32_t *r = status_ok(res, len);
	free(res);
	return r;
}

/* names, each followed by a NUL (a file name can contain anything else) */
uint32_t *rt_fs_list(StrBuf *path, uint64_t *len) {
	char *p = sb_cstr(path);
	DIR *d = opendir(p);
	int e = errno;
	free(p);
	if (!d) return status_errno(e, len);
	size_t cap = 256, n = 0;
	unsigned char *buf = (unsigned char *)malloc(cap);
	struct dirent *ent;
	while ((ent = readdir(d)) != NULL) {
		if (!strcmp(ent->d_name, ".") || !strcmp(ent->d_name, "..")) continue;
		size_t l = strlen(ent->d_name) + 1;
		while (n + l > cap) {
			cap *= 2;
			buf = (unsigned char *)realloc(buf, cap);
			if (!buf) exit(101);
		}
		memcpy(buf + n, ent->d_name, l);
		n += l;
	}
	closedir(d);
	uint32_t *r = status_bytes(0, buf, n, 0, len);
	free(buf);
	return r;
}

/* ------------------------------------------------------------------------- *
 * Time and randomness
 * ------------------------------------------------------------------------- */

double rt_time_unix(void) {
	struct timespec ts;
	clock_gettime(CLOCK_REALTIME, &ts);
	return (double)ts.tv_sec + (double)ts.tv_nsec / 1e9;
}
double rt_time_mono(void) {
	struct timespec ts;
	clock_gettime(CLOCK_MONOTONIC, &ts);
	return (double)ts.tv_sec + (double)ts.tv_nsec / 1e9;
}
/* seconds east of UTC in the local time zone at unix time t */
int32_t rt_time_offset(double t) {
	time_t tt = (time_t)t;
	struct tm tmv;
	tzset();
	if (!localtime_r(&tt, &tmv)) return 0;
	return (int32_t)tmv.tm_gmtoff;
}
void rt_time_sleep(int32_t ms) {
	if (ms <= 0) return;
	fflush(stdout);
	struct timespec req = {ms / 1000, (long)(ms % 1000) * 1000000L}, rem;
	while (nanosleep(&req, &rem) != 0 && errno == EINTR) req = rem;
}
int32_t rt_rng_seed(void) {
	uint32_t v = 0;
	int fd = open("/dev/urandom", O_RDONLY);
	if (fd >= 0) {
		ssize_t r = read(fd, &v, sizeof v);
		(void)r;
		close(fd);
	}
	if (!v) v = (uint32_t)time(NULL) ^ (uint32_t)getpid();
	return (int32_t)v;
}

/* ------------------------------------------------------------------------- *
 * Terminal
 *
 * Raw mode keeps output processing on (so "\n" still ends a line) but turns off line
 * editing, echo and signal keys: Ctrl-C arrives as the key 3. It is restored on exit,
 * on `exit`, and from the fault handler. SIGWINCH is only hooked once a terminal
 * primitive is used, so programs that never touch the terminal see no extra EINTRs.
 * ------------------------------------------------------------------------- */

#define KEY_BASE 0x110000
enum { K_UP = 1, K_DOWN, K_RIGHT, K_LEFT, K_HOME, K_END, K_INSERT, K_DELETE, K_PGUP, K_PGDN,
       K_F1 = 16, K_RESIZE = 255 };

static struct termios term_orig;
static int term_have_orig, term_is_raw;

static void term_restore(void) {
	if (term_is_raw && term_have_orig) {
		tcsetattr(0, TCSAFLUSH, &term_orig); /* async-signal-safe */
		term_is_raw = 0;
	}
}

/* A signal that would kill the program (kill, a closed window, Ctrl-C from another
 * terminal) must not leave the user's terminal in raw mode. */
static void on_fatal_signal(int sig) {
	term_restore();
	signal(sig, SIG_DFL);
	raise(sig);
}

static int term_sigs_installed;
static void term_install_fatal_handlers(void) {
	if (term_sigs_installed) return;
	term_sigs_installed = 1;
	static const int sigs[] = {SIGINT, SIGTERM, SIGHUP, SIGQUIT};
	for (size_t i = 0; i < sizeof sigs / sizeof sigs[0]; i++) {
		struct sigaction sa;
		memset(&sa, 0, sizeof sa);
		sa.sa_handler = on_fatal_signal;
		sigemptyset(&sa.sa_mask);
		sigaction(sigs[i], &sa, NULL);
	}
}

static void on_winch(int sig) {
	(void)sig;
	winch_flag = 1;
}

static void term_init(void) {
	if (term_inited) return;
	term_inited = 1;
	struct sigaction sa;
	memset(&sa, 0, sizeof sa);
	sa.sa_handler = on_winch;
	sigemptyset(&sa.sa_mask);
	sa.sa_flags = 0; /* no SA_RESTART: a resize must interrupt a blocked key read */
	sigaction(SIGWINCH, &sa, NULL);
	atexit(term_restore);
}

int32_t rt_term_is_tty(int32_t fd) {
	return isatty(fd) ? 1 : 0;
}

int32_t rt_term_raw(int32_t on) {
	term_init();
	if (!isatty(0)) return -1;
	if (!on) {
		if (term_is_raw && tcsetattr(0, TCSAFLUSH, &term_orig) != 0) return -1;
		term_is_raw = 0;
		return 0;
	}
	if (term_is_raw) return 0;
	term_install_fatal_handlers();
	if (!term_have_orig) {
		if (tcgetattr(0, &term_orig) != 0) return -1;
		term_have_orig = 1;
	}
	struct termios t = term_orig;
	t.c_iflag &= ~(tcflag_t)(IXON | ICRNL | INLCR | BRKINT | INPCK | ISTRIP);
	t.c_lflag &= ~(tcflag_t)(ICANON | ECHO | IEXTEN | ISIG);
	t.c_cc[VMIN] = 1;
	t.c_cc[VTIME] = 0;
	fflush(stdout);
	if (tcsetattr(0, TCSAFLUSH, &t) != 0) return -1;
	term_is_raw = 1;
	return 0;
}

static int term_size(int *cols, int *rows) {
	struct winsize ws;
	static const int fds[3] = {1, 0, 2};
	for (int i = 0; i < 3; i++) {
		if (isatty(fds[i]) && ioctl(fds[i], TIOCGWINSZ, &ws) == 0 && ws.ws_col > 0 && ws.ws_row > 0) {
			*cols = ws.ws_col;
			*rows = ws.ws_row;
			return 1;
		}
	}
	const char *c = getenv("COLUMNS"), *r = getenv("LINES");
	*cols = (c && atoi(c) > 0) ? atoi(c) : 80;
	*rows = (r && atoi(r) > 0) ? atoi(r) : 24;
	return 0;
}
int32_t rt_term_cols(void) {
	term_init();
	int c, r;
	term_size(&c, &r);
	return c;
}
int32_t rt_term_rows(void) {
	term_init();
	int c, r;
	term_size(&c, &r);
	return r;
}
/* whether the terminal was resized since the last call (clears the flag) */
int32_t rt_term_resized(void) {
	term_init();
	int f = winch_flag;
	winch_flag = 0;
	return f ? 1 : 0;
}

/* The next byte within `ms` milliseconds, or -1 */
static int next_byte_within(int ms) {
	int r = in_fill(ms, 0);
	return r > 0 ? in_buf[in_pos++] : -1;
}

/* Result of decoding what follows an ESC: a key code, or this to say "a complete sequence
 * that we do not know; skip it and read the next key". */
#define K_SKIP (-3)

/* A decoded escape sequence (the ESC is already consumed). A byte that does not continue a
 * sequence is left in the buffer, so Alt+x or ESC ESC still deliver the second key. */
static int32_t decode_escape(void) {
	int b = next_byte_within(25);
	if (b < 0) return 27; /* a bare Escape key */
	if (b == 'O') { /* SS3: F1..F4, and arrows in application mode */
		int c = next_byte_within(25);
		switch (c) {
		case 'A': return KEY_BASE + K_UP;
		case 'B': return KEY_BASE + K_DOWN;
		case 'C': return KEY_BASE + K_RIGHT;
		case 'D': return KEY_BASE + K_LEFT;
		case 'H': return KEY_BASE + K_HOME;
		case 'F': return KEY_BASE + K_END;
		case 'P': case 'Q': case 'R': case 'S': return KEY_BASE + K_F1 + (c - 'P');
		default: return K_SKIP;
		}
	}
	if (b != '[') {
		in_pos--; /* not a sequence: hand the byte back */
		return 27;
	}
	int params[4] = {0, 0, 0, 0}, np = 0, cur = -1, c;
	while ((c = next_byte_within(25)) >= 0) {
		if (c >= '0' && c <= '9') {
			cur = (cur < 0 ? 0 : cur) * 10 + (c - '0');
		}
		else if (c == ';') {
			if (np < 4) params[np++] = cur < 0 ? 0 : cur;
			cur = -1;
		}
		else break; /* final byte */
	}
	if (np < 4) params[np++] = cur < 0 ? 0 : cur;
	switch (c) {
	case 'A': return KEY_BASE + K_UP;
	case 'B': return KEY_BASE + K_DOWN;
	case 'C': return KEY_BASE + K_RIGHT;
	case 'D': return KEY_BASE + K_LEFT;
	case 'H': return KEY_BASE + K_HOME;
	case 'F': return KEY_BASE + K_END;
	case '~':
		switch (params[0]) {
		case 1: case 7: return KEY_BASE + K_HOME;
		case 2: return KEY_BASE + K_INSERT;
		case 3: return KEY_BASE + K_DELETE;
		case 4: case 8: return KEY_BASE + K_END;
		case 5: return KEY_BASE + K_PGUP;
		case 6: return KEY_BASE + K_PGDN;
		case 11: case 12: case 13: case 14: case 15: return KEY_BASE + K_F1 + (params[0] - 11);
		case 17: case 18: case 19: case 20: case 21: return KEY_BASE + K_F1 + 5 + (params[0] - 17);
		case 23: case 24: return KEY_BASE + K_F1 + 10 + (params[0] - 23);
		default: return K_SKIP;
		}
	default: return K_SKIP;
	}
}

/* One key: a Unicode code point, or KEY_BASE + a K_* code. -1 on timeout, -2 at the end
 * of the input. timeout_ms < 0 waits forever. A resize is reported as K_RESIZE. */
int32_t rt_term_key(int32_t timeout_ms) {
	term_init();
	fflush(stdout);
	if (winch_flag) {
		winch_flag = 0;
		return KEY_BASE + K_RESIZE;
	}
	int r = in_fill(timeout_ms, 1);
	if (r == -2) {
		winch_flag = 0;
		return KEY_BASE + K_RESIZE;
	}
	if (r == -1) return -1;
	if (r == 0) return -2;
	int b = in_buf[in_pos++];
	if (b == 27) {
		int32_t k = decode_escape();
		if (k == K_SKIP) return rt_term_key(timeout_ms); /* an unknown sequence: next key */
		return k;
	}
	if (b < 0x80) return b;
	int extra = (b >> 5) == 6 ? 1 : (b >> 4) == 14 ? 2 : (b >> 3) == 30 ? 3 : -1;
	if (extra < 0) return 0xFFFD;
	uint32_t cp = extra == 1 ? (b & 0x1F) : extra == 2 ? (b & 0x0F) : (b & 0x07);
	for (int k = 0; k < extra; k++) {
		int c = next_byte_within(50);
		if (c < 0 || (c & 0xC0) != 0x80) return 0xFFFD;
		cp = (cp << 6) | (c & 0x3F);
	}
	return (int32_t)cp;
}

/* ------------------------------------------------------------------------- *
 * Child processes
 *
 * `spec` is the program followed by its arguments, each terminated by a NUL; the program
 * is looked up on $PATH. mode 0 captures stdout and stderr (stdin is fed from `input`),
 * mode 1 lets the child share our terminal, mode 2 captures stdout only.
 * Result payload: "<exit code>\0" and, when capturing, "<stdout length>\0<stdout><stderr>"
 * (lengths in characters). A child killed by a signal reports 128 + the signal.
 * ------------------------------------------------------------------------- */

typedef struct {
	unsigned char *d;
	size_t n, cap;
} Bytes;
static void bytes_add(Bytes *b, const unsigned char *s, size_t n) {
	if (b->n + n > b->cap) {
		b->cap = (b->n + n) * 2 + 64;
		b->d = (unsigned char *)realloc(b->d, b->cap);
		if (!b->d) exit(101);
	}
	memcpy(b->d + b->n, s, n);
	b->n += n;
}

uint32_t *rt_proc_run(StrBuf *spec, StrBuf *input, int32_t mode, uint64_t *len) {
	size_t spec_n, in_n;
	char *sp = sb_take(spec, &spec_n, 0);
	char *in = sb_take(input, &in_n, 0);
	int argc = 0;
	for (size_t i = 0; i < spec_n; i++)
		if (sp[i] == 0) argc++;
	char **argv = (char **)calloc((size_t)argc + 1, sizeof(char *));
	{
		size_t i = 0;
		for (int k = 0; k < argc; k++) {
			argv[k] = sp + i;
			i += strlen(sp + i) + 1;
		}
	}
	if (argc == 0) {
		free(argv);
		free(sp);
		free(in);
		return status_msg(E_INVALID, "no program to run", len);
	}
	int capture = mode != 1;
	int out_p[2] = {-1, -1}, err_p[2] = {-1, -1}, in_p[2] = {-1, -1}, exec_p[2];
	if (pipe(exec_p) != 0 || (capture && (pipe(out_p) != 0 || pipe(in_p) != 0 || (mode == 0 && pipe(err_p) != 0)))) {
		int e = errno;
		free(argv); free(sp); free(in);
		return status_errno(e, len);
	}
	fcntl(exec_p[1], F_SETFD, FD_CLOEXEC);
	fflush(stdout);
	fflush(stderr);
	pid_t pid = fork();
	if (pid < 0) {
		int e = errno;
		free(argv); free(sp); free(in);
		return status_errno(e, len);
	}
	if (pid == 0) {
		if (capture) {
			dup2(in_p[0], 0);
			dup2(out_p[1], 1);
			if (mode == 0) dup2(err_p[1], 2);
			int fds[6] = {in_p[0], in_p[1], out_p[0], out_p[1], err_p[0], err_p[1]};
			for (int i = 0; i < 6; i++) if (fds[i] > 2) close(fds[i]);
		}
		close(exec_p[0]);
		execvp(argv[0], argv);
		int e = errno;
		ssize_t w = write(exec_p[1], &e, sizeof e);
		(void)w;
		_exit(127);
	}
	close(exec_p[1]);
	if (capture) {
		close(in_p[0]);
		close(out_p[1]);
		if (mode == 0) close(err_p[1]);
	}
	/* did exec fail? */
	int child_err = 0;
	ssize_t er;
	do er = read(exec_p[0], &child_err, sizeof child_err); while (er < 0 && errno == EINTR);
	close(exec_p[0]);

	Bytes out = {0}, err = {0};
	if (capture && er == 0) {
		struct sigaction ign, old;
		memset(&ign, 0, sizeof ign);
		ign.sa_handler = SIG_IGN;
		sigemptyset(&ign.sa_mask);
		sigaction(SIGPIPE, &ign, &old);
		size_t woff = 0;
		int in_fd = in_p[1], out_fd = out_p[0], err_fd = mode == 0 ? err_p[0] : -1;
		/* a blocking write of a big input would stall while the child waits for us to read */
		fcntl(in_fd, F_SETFL, fcntl(in_fd, F_GETFL) | O_NONBLOCK);
		if (in_n == 0) { close(in_fd); in_fd = -1; }
		unsigned char tmp[8192];
		while (in_fd >= 0 || out_fd >= 0 || err_fd >= 0) {
			struct pollfd p[3];
			int np = 0, which[3];
			if (in_fd >= 0) { p[np] = (struct pollfd){in_fd, POLLOUT, 0}; which[np++] = 0; }
			if (out_fd >= 0) { p[np] = (struct pollfd){out_fd, POLLIN, 0}; which[np++] = 1; }
			if (err_fd >= 0) { p[np] = (struct pollfd){err_fd, POLLIN, 0}; which[np++] = 2; }
			if (poll(p, (nfds_t)np, -1) < 0) {
				if (errno == EINTR) continue;
				break;
			}
			for (int i = 0; i < np; i++) {
				if (!p[i].revents) continue;
				if (which[i] == 0) {
					ssize_t w = write(in_fd, in + woff, in_n - woff);
					if (w > 0) woff += (size_t)w;
					if (w < 0 && errno != EINTR && errno != EAGAIN) woff = in_n; /* the child stopped reading */
					if (woff >= in_n) { close(in_fd); in_fd = -1; }
				}
				else {
					int fd = which[i] == 1 ? out_fd : err_fd;
					ssize_t r = read(fd, tmp, sizeof tmp);
					if (r > 0) bytes_add(which[i] == 1 ? &out : &err, tmp, (size_t)r);
					else if (r == 0 || (errno != EINTR && errno != EAGAIN)) {
						close(fd);
						if (which[i] == 1) out_fd = -1; else err_fd = -1;
					}
				}
			}
		}
		if (in_fd >= 0) close(in_fd);
		if (out_fd >= 0) close(out_fd);
		if (err_fd >= 0) close(err_fd);
		sigaction(SIGPIPE, &old, NULL);
	}
	else if (capture) { /* exec failed: nothing will ever be read or written */
		close(in_p[1]);
		close(out_p[0]);
		if (err_p[0] >= 0) close(err_p[0]);
	}
	int st = 0;
	while (waitpid(pid, &st, 0) < 0 && errno == EINTR) {}
	free(argv); free(sp); free(in);
	if (er > 0) {
		free(out.d); free(err.d);
		return status_errno(child_err, len); /* could not start the program */
	}
	int code = WIFEXITED(st) ? WEXITSTATUS(st) : WIFSIGNALED(st) ? 128 + WTERMSIG(st) : 255;

	/* payload (as bytes -> code points) */
	uint32_t *res;
	if (!capture) {
		char hdr[32];
		snprintf(hdr, sizeof hdr, "%d", code);
		size_t hl = strlen(hdr) + 1;
		res = rt_buf_alloc(1 + hl);
		res[0] = 0;
		for (size_t i = 0; i < hl; i++) res[1 + i] = (unsigned char)hdr[i];
		*len = 1 + hl;
		return res;
	}
	uint32_t *o = rt_buf_alloc(out.n ? out.n : 1), *e = rt_buf_alloc(err.n ? err.n : 1);
	uint64_t on = utf8_decode(out.d ? out.d : (const unsigned char *)"", out.n, o);
	uint64_t en = utf8_decode(err.d ? err.d : (const unsigned char *)"", err.n, e);
	/* the header contains NULs, so build it by hand */
	char h1[16], h2[24];
	int l1 = snprintf(h1, sizeof h1, "%d", code);
	int l2 = snprintf(h2, sizeof h2, "%llu", (unsigned long long)on);
	size_t total = 1 + (size_t)l1 + 1 + (size_t)l2 + 1 + on + en;
	res = rt_buf_alloc(total);
	size_t k = 0;
	res[k++] = 0;
	for (int i = 0; i < l1; i++) res[k++] = (unsigned char)h1[i];
	res[k++] = 0;
	for (int i = 0; i < l2; i++) res[k++] = (unsigned char)h2[i];
	res[k++] = 0;
	for (uint64_t i = 0; i < on; i++) res[k++] = o[i];
	for (uint64_t i = 0; i < en; i++) res[k++] = e[i];
	rt_free(o); rt_free(e);
	free(out.d); free(err.d);
	*len = total;
	return res;
}

/* ------------------------------------------------------------------------- *
 * Program entry
 *
 * The runtime is single-threaded. Non-tail recursion (and a long chain of thunks)
 * uses the native stack, so the program runs on a separate, very large stack
 * switched to with ucontext (still one thread). The stack is reserved with mmap
 * and only committed as it's touched. IOTA_STACK_MB overrides the default
 * (4096 MB); if the OS refuses, the request is halved until it works. Running
 * out anyway is reported instead of crashing with a bare segfault because fuck that.
 * ------------------------------------------------------------------------- */

extern int32_t iota_main(void);

static int32_t exit_status = 0;
static ucontext_t main_ctx, prog_ctx;
static char *altstack_mem;

static void run_program(void) {
	exit_status = iota_main();
	fflush(stdout);
}

/* program's stack: [prog_lo, prog_lo + prog_size), low `prog_guard` bytes protected */
static uintptr_t prog_lo, prog_size, prog_guard;
static volatile sig_atomic_t in_fault;

#define WR(lit) do { ssize_t r_ = write(2, lit, sizeof lit - 1); (void)r_; } while (0)

static void wr_hex(uintptr_t v) {
	char buf[2 + 2 * sizeof(uintptr_t)];
	size_t i = sizeof buf;
	do {
		buf[--i] = "0123456789abcdef"[v & 15];
		v >>= 4;
	} while (v);
	buf[--i] = 'x';
	buf[--i] = '0';
	ssize_t r = write(2, buf + i, sizeof buf - i);
	(void)r;
}

/* A frame bigger than the guard can jump over it and fault below the mapping;
 * treat that much of the space under the stack as "still an overflow". */
#define OVERSHOOT ((uintptr_t)1 << 20)

static void on_fault(int sig, siginfo_t *si, void *ctx) {
	(void)ctx;
	if (in_fault) _exit(105); /* a fault inside the handler: give up immediately */
	in_fault = 1;
	term_restore();
	/* keep what the program already printed (rt_fail does the same). stdio is
	 * normally not mid-operation here: overflow happens in generated code. */
	fflush(stdout);

	uintptr_t a = (uintptr_t)si->si_addr;
	if (prog_guard && a + OVERSHOOT >= prog_lo && a < prog_lo + prog_guard) {
		WR("iota: runtime error: stack overflow (raise it with IOTA_STACK_MB)\n");
		_exit(103);
	}
	if (prog_size && a >= prog_lo + prog_guard && a < prog_lo + prog_size) {
		WR("iota: runtime error: could not grow the stack (out of memory?)\n");
		_exit(101);
	}
	WR("iota: internal error: ");
	if (sig == SIGBUS) {
		WR("bus error");
	} else {
		WR("segmentation fault");
	};
	WR(" at address ");
	wr_hex(a);
	WR("\n  this is a bug in the Iota compiler or runtime, not in your program\n");
	WR("  (IOTA_NO_SEGV_HANDLER=1 disables this handler: core dump / debugger)\n");
	_exit(105);
}

static void print_stats(void) {
	struct timespec now;
	clock_gettime(CLOCK_MONOTONIC, &now);
	struct rusage ru;
	getrusage(RUSAGE_SELF, &ru);
	double wall = (double)(now.tv_sec - st_start.tv_sec) + (double)(now.tv_nsec - st_start.tv_nsec) / 1e9;
	double user = (double)ru.ru_utime.tv_sec + (double)ru.ru_utime.tv_usec / 1e6;
	double sys = (double)ru.ru_stime.tv_sec + (double)ru.ru_stime.tv_usec / 1e6;
#ifdef __APPLE__
	double rss_mb = (double)ru.ru_maxrss / 1048576.0; /* bytes on macOS */
#else
	double rss_mb = (double)ru.ru_maxrss / 1024.0; /* kilobytes on Linux */
#endif
	fprintf(stderr,
		"[iota] allocs=%" PRIu64 " (%.1f MB) frees=%" PRIu64 " peak_live=%" PRIu64
		" wall=%.3fs user=%.3fs sys=%.3fs maxrss=%.1fMB\n",
		st_allocs, (double)st_bytes / 1048576.0, st_frees, st_peak, wall, user, sys, rss_mb);
}

int main(int argc, char **argv) {
	g_argc = argc;
	g_argv = argv;
	size_t mb = 4096;
	const char *e = getenv("IOTA_STACK_MB");
	if (e && atol(e) > 0) mb = (size_t)atol(e);

	/* the handler must run on its own stack to be able to report an overflow */
	size_t alt_size = 64 * 1024;
	altstack_mem = (char *)malloc(alt_size);
	stack_t ss;
	ss.ss_sp = altstack_mem;
	ss.ss_size = alt_size;
	ss.ss_flags = 0;
	sigaltstack(&ss, NULL);
	if (!getenv("IOTA_NO_SEGV_HANDLER")) {
		struct sigaction sa;
		memset(&sa, 0, sizeof sa);
		sa.sa_sigaction = on_fault;
		sa.sa_flags = SA_SIGINFO | SA_ONSTACK;
		sigemptyset(&sa.sa_mask);
		sigaction(SIGSEGV, &sa, NULL);
		sigaction(SIGBUS, &sa, NULL);
	}

	void *stack = MAP_FAILED;
	size_t size = 0;
	for (; mb >= 1 && stack == MAP_FAILED; mb /= 2) {
		size = mb << 20;
		stack = mmap(NULL, size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
	}
	if (stack == MAP_FAILED) {
		fputs("iota: cannot reserve a stack for the program\n", stderr);
		return 104;
	}

	/* guard region at the low end: PROT_NONE costs nothing (never committed) */
	size_t guard = (size_t)1 << 20;
	if (guard > size / 4) guard = size / 4;
	if (mprotect(stack, guard, PROT_NONE) != 0) guard = 0; /* no guard: do not claim overflows */
	prog_lo = (uintptr_t)stack;
	prog_size = size;
	prog_guard = guard;

	if (getenv("IOTA_STATS")) {
		clock_gettime(CLOCK_MONOTONIC, &st_start);
		atexit(print_stats);
	}

	getcontext(&prog_ctx);
	prog_ctx.uc_stack.ss_sp = (char *)stack + guard;
	prog_ctx.uc_stack.ss_size = size - guard;
	prog_ctx.uc_link = &main_ctx;
	makecontext(&prog_ctx, run_program, 0);
	swapcontext(&main_ctx, &prog_ctx);
	return exit_status;
}
