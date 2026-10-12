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

/* The generated code stores a constructor tag in the low bits of heap pointers, so
 * every object must be 16-byte aligned (malloc guarantees alignof(max_align_t)). */
void *rt_alloc(uint64_t n) {
	void *p = malloc(n ? n : 16);
	if (!p) {
		fputs("iota: out of memory\n", stderr);
		exit(101);
	}
	return p;
}
void rt_free(void *p) {
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

/* Int: div truncates; mod is Euclidean (always >= 0 for a positive divisor).
 * This matches the constant folder in optimize.rs, so
 * a folded and an unfolded computation can never disagree. */
int32_t rt_idiv(int32_t a, int32_t b) {
	if (b == 0) {
		fflush(stdout);
		fputs("iota: runtime error: division by zero\n", stderr);
		exit(104);
	}
	if (b == -1) return (int32_t)(0u - (uint32_t)a); /* avoids INT_MIN / -1 trap */
	return a / b;
}
int32_t rt_imod(int32_t a, int32_t b) {
	if (b == 0) {
		fflush(stdout);
		fputs("iota: runtime error: modulo by zero\n", stderr);
		exit(104);
	}
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
	free(b->data);
	free(b);
}

/* One line from stdin without the newline.
 * On EOF with no input, returns the empty string. */
uint32_t *rt_getln(uint64_t *len) {
	fflush(stdout);
	size_t cap = 128, n = 0;
	unsigned char *line = (unsigned char *)rt_alloc(cap);
	int c;
	while ((c = getchar()) != EOF && c != '\n') {
		if (n == cap) {
			cap *= 2;
			line = (unsigned char *)realloc(line, cap);
			if (!line) exit(101);
		}
		line[n++] = (unsigned char)c;
	}
	if (n && line[n - 1] == '\r') n--;
	uint32_t *out = rt_buf_alloc(n);
	uint64_t m = 0;
	for (size_t i = 0; i < n;) {
		unsigned char b = line[i];
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
			cp = 0xFFFD;
			extra = 0;
		}
		i++;
		for (int k = 0; k < extra && i < n; k++, i++) cp = (cp << 6) | (line[i] & 0x3F);
		out[m++] = cp;
	}
	free(line);
	*len = m;
	return out;
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

static void on_segv(int sig) {
	(void)sig;
	static const char msg[] = "iota: runtime error: stack overflow (raise it with IOTA_STACK_MB)\n";
	ssize_t r = write(2, msg, sizeof msg - 1);
	(void)r;
	_exit(103);
}

int main(void) {
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
	struct sigaction sa;
	memset(&sa, 0, sizeof sa);
	sa.sa_handler = on_segv;
	sa.sa_flags = SA_ONSTACK;
	sigemptyset(&sa.sa_mask);
	sigaction(SIGSEGV, &sa, NULL);

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
	getcontext(&prog_ctx);
	prog_ctx.uc_stack.ss_sp = stack;
	prog_ctx.uc_stack.ss_size = size;
	prog_ctx.uc_link = &main_ctx;
	makecontext(&prog_ctx, run_program, 0);
	swapcontext(&main_ctx, &prog_ctx);
	return exit_status;
}
