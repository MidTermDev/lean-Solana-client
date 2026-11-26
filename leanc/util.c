// Platform layer and small utilities. Everything the compiler needs from the
// outside world goes through the five raw Linux syscalls in this file.
#include "leanc.h"

static long sys(long n, long a, long b, long c, long d, long e, long f) {
  long ret;
  register long r10 __asm__("r10") = d;
  register long r8 __asm__("r8") = e;
  register long r9 __asm__("r9") = f;
  __asm__ volatile("syscall"
                   : "=a"(ret)
                   : "a"(n), "D"(a), "S"(b), "d"(c), "r"(r10), "r"(r8), "r"(r9)
                   : "rcx", "r11", "memory");
  return ret;
}

enum { SYS_read = 0, SYS_write = 1, SYS_open = 2, SYS_close = 3, SYS_mmap = 9, SYS_exit_group = 231 };

void *memcpy(void *d, const void *s, unsigned long n) {
  u8 *dp = d;
  const u8 *sp = s;
  while (n--) *dp++ = *sp++;
  return d;
}
void *memset(void *d, int c, unsigned long n) {
  u8 *dp = d;
  while (n--) *dp++ = (u8)c;
  return d;
}
int memcmp(const void *a, const void *b, unsigned long n) {
  const u8 *x = a, *y = b;
  for (; n--; x++, y++)
    if (*x != *y) return *x < *y ? -1 : 1;
  return 0;
}
unsigned long strlen(const char *s) {
  unsigned long n = 0;
  while (s[n]) n++;
  return n;
}

void plat_write(int fd, const void *buf, u64 len) {
  const char *p = buf;
  while (len > 0) {
    long r = sys(SYS_write, fd, (long)p, (long)len, 0, 0, 0);
    if (r <= 0) return;
    p += r;
    len -= (u64)r;
  }
}

void plat_exit(int code) {
  sys(SYS_exit_group, code, 0, 0, 0, 0, 0);
  for (;;) {
  }
}

static char *arena_cur, *arena_end;

void *xalloc(u64 size) {
  size = (size + 15) & ~15ull;
  if ((u64)(arena_end - arena_cur) < size) {
    u64 chunk = size > (8u << 20) ? size : (8u << 20);
    long p = sys(SYS_mmap, 0, (long)chunk, 3 /*RW*/, 0x22 /*PRIVATE|ANON*/, -1, 0);
    if (p < 0 && p > -4096) {
      plat_write(2, "leanc: out of memory\n", 21);
      plat_exit(1);
    }
    arena_cur = (char *)p;
    arena_end = arena_cur + chunk;
  }
  void *r = arena_cur; // fresh anonymous mappings are already zeroed
  arena_cur += size;
  return r;
}

char *plat_read_file(const char *path, u64 *len) {
  long fd = sys(SYS_open, (long)path, 0, 0, 0, 0, 0);
  if (fd < 0) return NULL;
  Buf b = {0};
  char tmp[65536];
  for (;;) {
    long r = sys(SYS_read, fd, (long)tmp, sizeof tmp, 0, 0, 0);
    if (r <= 0) break;
    buf_put(&b, tmp, (u64)r);
  }
  sys(SYS_close, fd, 0, 0, 0, 0, 0);
  buf_u8(&b, 0);
  *len = b.len - 1;
  return b.p;
}

bool plat_write_file(const char *path, const void *buf, u64 len, int mode) {
  long fd = sys(SYS_open, (long)path, 01 | 0100 | 01000 /*WRONLY|CREAT|TRUNC*/, mode, 0, 0, 0);
  if (fd < 0) return false;
  plat_write((int)fd, buf, len);
  sys(SYS_close, fd, 0, 0, 0, 0, 0);
  return true;
}

// ------------------------------------------------------------------ buffers
void buf_put(Buf *b, const void *data, u64 len) {
  if (b->len + len > b->cap) {
    u64 cap = b->cap ? b->cap * 2 : 256;
    while (cap < b->len + len) cap *= 2;
    char *p = xalloc(cap);
    memcpy(p, b->p, b->len);
    b->p = p;
    b->cap = cap;
  }
  memcpy(b->p + b->len, data, len);
  b->len += len;
}
void buf_u8(Buf *b, u8 v) { buf_put(b, &v, 1); }
void buf_u32(Buf *b, u32 v) { buf_put(b, &v, 4); }
void buf_u64(Buf *b, u64 v) { buf_put(b, &v, 8); }
void buf_str(Buf *b, const char *s) { buf_put(b, s, strlen(s)); }

static void put_num(Buf *b, u64 v, int base) {
  char tmp[32];
  int n = 0;
  do {
    int d = (int)(v % (u64)base);
    tmp[n++] = (char)(d < 10 ? '0' + d : 'a' + d - 10);
    v /= (u64)base;
  } while (v);
  while (n) buf_u8(b, (u8)tmp[--n]);
}

void buf_vfmt(Buf *b, const char *f, __builtin_va_list ap) {
  for (; *f; f++) {
    if (*f != '%') {
      buf_u8(b, (u8)*f);
      continue;
    }
    f++;
    bool lng = false;
    while (*f == 'l') {
      lng = true;
      f++;
    }
    switch (*f) {
    case 's': {
      const char *s = __builtin_va_arg(ap, const char *);
      buf_str(b, s ? s : "(null)");
      break;
    }
    case 'd': {
      i64 v = lng ? __builtin_va_arg(ap, i64) : (i64)__builtin_va_arg(ap, int);
      if (v < 0) {
        buf_u8(b, '-');
        v = -v;
      }
      put_num(b, (u64)v, 10);
      break;
    }
    case 'u': put_num(b, lng ? __builtin_va_arg(ap, u64) : (u64)__builtin_va_arg(ap, u32), 10); break;
    case 'x': put_num(b, lng ? __builtin_va_arg(ap, u64) : (u64)__builtin_va_arg(ap, u32), 16); break;
    case 'c': buf_u8(b, (u8)__builtin_va_arg(ap, int)); break;
    default: buf_u8(b, (u8)*f);
    }
  }
}

void buf_fmt(Buf *b, const char *f, ...) {
  __builtin_va_list ap;
  __builtin_va_start(ap, f);
  buf_vfmt(b, f, ap);
  __builtin_va_end(ap);
}

// ---------------------------------------------------------------- interning
typedef struct Sym {
  struct Sym *next;
  int len;
  char s[];
} Sym;
static Sym *symtab[1 << 14];

const char *intern_n(const char *s, int n) {
  u32 h = 2166136261u;
  for (int i = 0; i < n; i++) h = (h ^ (u8)s[i]) * 16777619u;
  Sym **slot = &symtab[h & ((1 << 14) - 1)];
  for (Sym *e = *slot; e; e = e->next)
    if (e->len == n && memcmp(e->s, s, (unsigned long)n) == 0) return e->s;
  Sym *e = xalloc(sizeof(Sym) + (u64)n + 1);
  e->len = n;
  memcpy(e->s, s, (unsigned long)n);
  e->next = *slot;
  *slot = e;
  return e->s;
}
const char *intern(const char *s) { return intern_n(s, (int)strlen(s)); }

const char *fmt(const char *f, ...) {
  Buf b = {0};
  __builtin_va_list ap;
  __builtin_va_start(ap, f);
  buf_vfmt(&b, f, ap);
  __builtin_va_end(ap);
  return intern_n(b.p ? b.p : "", (int)b.len);
}

bool str_starts(const char *s, const char *prefix) {
  while (*prefix)
    if (*s++ != *prefix++) return false;
  return true;
}

const char *str_rchr(const char *s, char c) {
  const char *r = NULL;
  for (; *s; s++)
    if (*s == c) r = s;
  return r;
}

// ------------------------------------------------------------------- errors
void fatal_at(const char *file, int line, int col, const char *f, ...) {
  Buf b = {0};
  buf_fmt(&b, "%s:%d:%d: error: ", file ? file : "?", line, col);
  __builtin_va_list ap;
  __builtin_va_start(ap, f);
  buf_vfmt(&b, f, ap);
  __builtin_va_end(ap);
  buf_u8(&b, '\n');
  plat_write(2, b.p, b.len);
  plat_exit(1);
}

void fatal(const char *f, ...) {
  Buf b = {0};
  buf_str(&b, "leanc: error: ");
  __builtin_va_list ap;
  __builtin_va_start(ap, f);
  buf_vfmt(&b, f, ap);
  __builtin_va_end(ap);
  buf_u8(&b, '\n');
  plat_write(2, b.p, b.len);
  plat_exit(1);
}
