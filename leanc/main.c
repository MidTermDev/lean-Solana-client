// leanc driver: load modules, elaborate from `main`, emit an ELF executable.
#include "leanc.h"

bool opt_verbose;

static const char *include_dirs[32];
static int ninclude;

typedef struct Loaded {
  const char *name;
  struct Loaded *next;
} Loaded;
static Loaded *loaded;

static const char *dir_of(const char *path) {
  const char *slash = str_rchr(path, '/');
  return slash ? intern_n(path, (int)(slash - path)) : intern(".");
}

static void load_file(const char *path);

static void load_module(const char *name, const char *from) {
  for (Loaded *l = loaded; l; l = l->next)
    if (l->name == name) return;
  Loaded *l = xalloc(sizeof *l);
  l->name = name;
  l->next = loaded;
  loaded = l;
  Buf rel = {0};
  for (const char *s = name; *s; s++) buf_u8(&rel, *s == '.' ? '/' : (u8)*s);
  buf_str(&rel, ".lean");
  buf_u8(&rel, 0);
  for (int i = 0; i < ninclude; i++) {
    const char *path = fmt("%s/%s", include_dirs[i], rel.p);
    u64 len;
    char *src = plat_read_file(path, &len);
    if (src) {
      load_file(path);
      return;
    }
  }
  fatal("%s: cannot find module '%s' (searched %d include directories; add one with -I)", from, name, ninclude);
}

static void load_file(const char *path) {
  u64 len;
  char *src = plat_read_file(path, &len);
  if (!src) fatal("cannot read '%s'", path);
  Module m = parse_module(intern(path), src, len);
  for (int i = 0; i < m.nimports; i++) load_module(m.imports[i], path);
  elab_add_module(&m);
}

static const char *usage =
    "leanc - a zero-dependency Lean 4 (subset) to x86-64 Linux compiler\n"
    "\n"
    "usage: leanc [options] Main.lean\n"
    "  -o FILE   output executable (default: a.out)\n"
    "  -I DIR    add a module search directory (the runtime Rt.lean must be on it)\n"
    "  -v        print statistics\n";

static int real_main(int argc, char **argv) {
  const char *out = "a.out", *input = NULL;
  for (int i = 1; i < argc; i++) {
    const char *a = argv[i];
    if (a[0] == '-' && a[1] == 'o' && !a[2] && i + 1 < argc) out = argv[++i];
    else if (a[0] == '-' && a[1] == 'I' && !a[2] && i + 1 < argc) include_dirs[ninclude++] = intern(argv[++i]);
    else if (a[0] == '-' && a[1] == 'I' && a[2]) include_dirs[ninclude++] = intern(a + 2);
    else if (a[0] == '-' && a[1] == 'v' && !a[2]) opt_verbose = true;
    else if (a[0] == '-') {
      plat_write(2, usage, strlen(usage));
      return 2;
    } else input = a;
    if (ninclude >= 30) fatal("too many -I directories");
  }
  if (!input) {
    plat_write(2, usage, strlen(usage));
    return 2;
  }
  types_init();
  elab_init();
  include_dirs[ninclude++] = dir_of(input);

  load_module(intern("Rt"), "leanc");
  load_file(input);

  static const char *needed[] = {"Rt.alloc", "Rt.free", "Rt.panic", "Rt.panicMsg", "Rt.arrUnique", "Rt.baUnique",
                                 "Rt.objUnique", "Rt.arrNew", "Rt.arrPush", "Rt.baPush", "Rt.arrReplicate", NULL};
  for (int i = 0; needed[i]; i++) elab_require(needed[i]);
  Func *main_fn = elab_find_func("main");
  if (!main_fn) fatal("%s: no 'main' definition (expected `def main : IO Unit`)", input);
  elab_require("main");
  if (main_fn->nparams) fatal("%s: main must take no parameters (use Sys.args for the command line)", input);

  for (int i = 0; i < nwork; i++) elab_func(work[i]);
  elab_finish_decls();
  for (int i = 0; i < nwork; i++) live_func(work[i]->body, work[i]->vars, work[i]->nvars);
  for (int i = 0; i < ngwork; i++) live_func(gwork[i]->init, gwork[i]->vars, gwork[i]->nvars);

  Buf elf = {0};
  gen_program(main_fn, &elf);
  if (!plat_write_file(out, elf.p, elf.len, 0755)) fatal("cannot write '%s'", out);
  if (opt_verbose) {
    Buf b = {0};
    buf_fmt(&b, "leanc: %s: %d functions, %d constants, %lu bytes\n", out, nwork, ngwork, elf.len);
    plat_write(2, b.p, b.len);
  }
  return 0;
}

#ifdef LEANC_HOSTED
int main(int argc, char **argv) { return real_main(argc, argv); }
#else
// No libc: the kernel jumps straight here with argc/argv on the stack.
__attribute__((used)) static void start_c(long *sp) { plat_exit(real_main((int)sp[0], (char **)(sp + 1))); }
__asm__(".globl _start\n_start:\n  xor %ebp, %ebp\n  mov %rsp, %rdi\n  and $-16, %rsp\n  call start_c\n");
#endif
