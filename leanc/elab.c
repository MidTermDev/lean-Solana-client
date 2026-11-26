// Elaborator: AST -> typed IR.
//
// This is a bidirectional type checker for a monomorphic, first-order
// fragment of Lean 4. It is deliberately not a proof checker: the official
// toolchain decides whether a program is well-typed Lean, leanc only has to
// agree with it on the programs it accepts and compile them faithfully.
#include "leanc.h"

static const char *S(const char *s) { return intern(s); }

// ------------------------------------------------------------------ tables
typedef struct MapEnt {
  const char *key;
  void *val;
  struct MapEnt *next;
} MapEnt;
typedef struct {
  MapEnt *b[1024];
} Map;

static void *map_get(Map *m, const char *key) {
  for (MapEnt *e = m->b[((u64)key >> 4) & 1023]; e; e = e->next)
    if (e->key == key) return e->val;
  return NULL;
}
static void map_put(Map *m, const char *key, void *val) {
  MapEnt *e = xalloc(sizeof *e);
  e->key = key;
  e->val = val;
  MapEnt **slot = &m->b[((u64)key >> 4) & 1023];
  e->next = *slot;
  *slot = e;
}

typedef struct {
  TypeDecl *td;
  int tag;
} CtorRef;

static Map funcs, globals, typedecls, aliases, ctors;
StrLit *strlits;
int nstrlits;
static int capstrlits;
Global *globals_head;
int nglobals;
Func **work;
int nwork;
static int capwork;
Global **gwork;
int ngwork;
static int capgwork;

typedef struct {
  Node *node; // N_ALIAS
} Alias;

int intern_strlit(const char *bytes, int len) {
  for (int i = 0; i < nstrlits; i++)
    if (strlits[i].len == len && memcmp(strlits[i].bytes, bytes, (unsigned long)len) == 0) return i;
  if (nstrlits == capstrlits) {
    int cap = capstrlits ? capstrlits * 2 : 64;
    StrLit *n = xalloc(sizeof(StrLit) * (u64)cap);
    memcpy(n, strlits, sizeof(StrLit) * (u64)nstrlits);
    strlits = n;
    capstrlits = cap;
  }
  char *copy = xalloc((u64)len + 1);
  memcpy(copy, bytes, (unsigned long)len);
  strlits[nstrlits].bytes = copy;
  strlits[nstrlits].len = len;
  return nstrlits++;
}

// ------------------------------------------------------------- elaboration context
typedef struct {
  const char *name;
  Var *var;
} ScopeEnt;

typedef struct Ctx {
  Node *decl; // declaration being elaborated (namespace context)
  ScopeEnt scope[1024];
  int nscope;
  Var **vars;
  int nvars, capvars;
  Expr *block; // innermost term-level do block
  int loop_depth;
} Ctx;
static Ctx *cx;

static void error_at(Node *at, const char *f, ...) __attribute__((noreturn));
static void error_at(Node *at, const char *f, ...) {
  Buf b = {0};
  __builtin_va_list ap;
  __builtin_va_start(ap, f);
  buf_vfmt(&b, f, ap);
  __builtin_va_end(ap);
  buf_u8(&b, 0);
  fatal_at(at->file, at->line, at->col, "%s", b.p);
}

static Expr *mke(int kind, Type *type, Node *at) {
  Expr *e = xalloc(sizeof(Expr));
  e->kind = kind;
  e->type = type;
  e->line = at ? at->line : 0;
  return e;
}

static Expr *mk_int(u64 v, Type *t, Node *at) {
  Expr *e = mke(E_INT, t, at);
  int bits = ty_bits(t);
  e->num = bits >= 64 ? v : v & ((1ull << bits) - 1);
  return e;
}

static Expr *mk_unit(Node *at) { return mke(E_UNIT, ty_unit, at); }

static Expr *mk_op(int op, Type *t, Node *at, int n, Expr *a, Expr *b, Expr *c) {
  Expr *e = mke(E_OP, t, at);
  e->num = (u64)op;
  e->nargs = n;
  e->args = xalloc(sizeof(Expr *) * 4);
  e->args[0] = a;
  e->args[1] = b;
  e->args[2] = c;
  return e;
}

static Var *new_var(const char *name, Type *type, bool is_mut) {
  Var *v = xalloc(sizeof(Var));
  v->name = name;
  v->type = ty_strip(type);
  v->is_mut = is_mut;
  v->hidden = name == NULL;
  if (cx->nvars == cx->capvars) {
    int cap = cx->capvars ? cx->capvars * 2 : 16;
    Var **n = xalloc(sizeof(Var *) * (u64)cap);
    memcpy(n, cx->vars, sizeof(Var *) * (u64)cx->nvars);
    cx->vars = n;
    cx->capvars = cap;
  }
  v->id = cx->nvars;
  cx->vars[cx->nvars++] = v;
  return v;
}

static void bind(Var *v, Node *at) {
  if (cx->nscope == 1024) error_at(at, "too many nested variables");
  cx->scope[cx->nscope].name = v->name;
  cx->scope[cx->nscope++].var = v;
}

static Var *find_local(const char *name) {
  for (int i = cx->nscope - 1; i >= 0; i--)
    if (cx->scope[i].name == name) return cx->scope[i].var;
  return NULL;
}

static Expr *mk_local(Var *v, Node *at) {
  Expr *e = mke(E_LOCAL, v->type, at);
  e->var = v;
  return e;
}

static Expr *mk_let(Var *v, Expr *init, Expr *body, Node *at) {
  Expr *e = mke(E_LET, body->type, at);
  e->var = v;
  e->a = init;
  e->b = body;
  return e;
}

// ------------------------------------------------------------------- types
static TypeDecl *find_typedecl(const char *name, Node *ctx);
static Type *resolve_type(Node *n, Node *ctx, bool allow_io);

static void resolve_decl(TypeDecl *td) {
  if (td->resolved || td->resolving) return;
  td->resolving = true;
  Node *n = td->node;
  if (n->kind == N_STRUCTDECL) {
    td->nctors = 1;
    td->ctors = xalloc(sizeof(Ctor));
    td->ctors[0].name = S("mk");
    td->ctors[0].nfields = n->n;
    td->ctors[0].fields = xalloc(sizeof(Field) * (u64)(n->n + 1));
    for (int i = 0; i < n->n; i++) {
      td->ctors[0].fields[i].name = n->list[i]->name;
      td->ctors[0].fields[i].type = resolve_type(n->list[i]->type, n, false);
      td->ctors[0].fields[i].dflt = n->list[i]->a;
    }
  } else {
    for (int c = 0; c < n->n; c++) {
      Node *cn = n->list[c];
      td->ctors[c].nfields = cn->n;
      td->ctors[c].fields = xalloc(sizeof(Field) * (u64)(cn->n + 1));
      for (int i = 0; i < cn->n; i++) {
        td->ctors[c].fields[i].name = cn->list[i]->name;
        td->ctors[c].fields[i].type = resolve_type(cn->list[i]->type, n, false);
      }
    }
  }
  td->resolved = true;
}

static Type *decl_type(TypeDecl *td) {
  resolve_decl(td);
  return td->type;
}

// Candidate fully-qualified names for `name` seen from declaration `ctx`,
// most specific first. Calls `try` until it returns non-NULL.
static void *resolve_scoped(const char *name, Node *ctx, void *(*try)(const char *)) {
  void *r;
  if (ctx && ctx->ns && ctx->ns[0]) {
    const char *ns = ctx->ns;
    for (;;) {
      if ((r = try(fmt("%s.%s", ns, name)))) return r;
      const char *dot = str_rchr(ns, '.');
      if (!dot) break;
      ns = intern_n(ns, (int)(dot - ns));
    }
  }
  if ((r = try(name))) return r;
  if (ctx)
    for (int i = ctx->nopens - 1; i >= 0; i--)
      if ((r = try(fmt("%s.%s", ctx->opens[i], name)))) return r;
  return NULL;
}

static void *try_typedecl(const char *full) { return map_get(&typedecls, full); }
static void *try_alias(const char *full) { return map_get(&aliases, full); }

static TypeDecl *find_typedecl(const char *name, Node *ctx) { return resolve_scoped(name, ctx, try_typedecl); }

static Type *builtin_type(const char *name) {
  if (name == S("Nat")) return ty_nat;
  if (name == S("UInt8")) return ty_u8;
  if (name == S("UInt16")) return ty_u16;
  if (name == S("UInt32")) return ty_u32;
  if (name == S("UInt64")) return ty_u64;
  if (name == S("USize")) return ty_usize;
  if (name == S("Bool")) return ty_bool;
  if (name == S("Char")) return ty_char;
  if (name == S("Unit")) return ty_unit;
  if (name == S("String")) return ty_string;
  if (name == S("ByteArray")) return ty_bytes;
  return NULL;
}

static Type *resolve_type(Node *n, Node *ctx, bool allow_io) {
  if (n->kind == N_TYPROD) return ty_prod(resolve_type(n->a, ctx, false), resolve_type(n->b, ctx, false));
  if (n->kind == N_TYFUN) error_at(n, "function types are not supported by leanc (first-order code only)");
  if (n->n == 1) {
    if (n->name == S("Array")) return ty_array(resolve_type(n->list[0], ctx, false));
    if (n->name == S("Option")) return ty_option(resolve_type(n->list[0], ctx, false));
    if (n->name == S("IO")) {
      if (!allow_io) error_at(n, "IO actions cannot be stored in data; IO is only allowed as a return type");
      return ty_io(resolve_type(n->list[0], ctx, false));
    }
    error_at(n, "unsupported type constructor '%s'", n->name);
  }
  TypeDecl *td = find_typedecl(n->name, ctx);
  if (td) return decl_type(td);
  Alias *al = resolve_scoped(n->name, ctx, try_alias);
  if (al) return resolve_type(al->node->type, al->node, allow_io);
  Type *t = builtin_type(n->name);
  if (t) return t;
  error_at(n, "unknown type '%s'", n->name);
}

static const char *type_ns(Type *t) {
  t = ty_strip(t);
  switch (t->kind) {
  case K_STRUCT: case K_IND: case K_ENUM: return t->decl->name;
  case K_ARRAY: return S("Array");
  case K_OPTION: return S("Option");
  case K_PROD: return S("Prod");
  default: return intern(t->name);
  }
}

static bool ty_eq(Type *a, Type *b) { return ty_strip(a) == ty_strip(b); }

static void check_type(Expr *e, Type *expected, Node *at) {
  if (!expected || ty_strip(e->type)->kind == K_NEVER) return;
  if (!ty_eq(e->type, expected))
    error_at(at, "type mismatch: expected %s, got %s", ty_name(ty_strip(expected)), ty_name(ty_strip(e->type)));
}

// ------------------------------------------------------------ declarations
void elab_add_module(Module *m) {
  for (int i = 0; i < m->ndecls; i++) {
    Node *d = m->decls[i];
    switch (d->kind) {
    case N_STRUCTDECL:
    case N_INDDECL: {
      if (map_get(&typedecls, d->name)) error_at(d, "duplicate type '%s'", d->name);
      TypeDecl *td = xalloc(sizeof *td);
      td->name = d->name;
      td->node = d;
      td->is_struct = d->kind == N_STRUCTDECL;
      Type *t = xalloc(sizeof(Type));
      t->decl = td;
      td->type = t;
      if (td->is_struct) {
        t->kind = K_STRUCT;
        CtorRef *cr = xalloc(sizeof *cr);
        cr->td = td;
        map_put(&ctors, fmt("%s.mk", d->name), cr);
      } else {
        bool boxed = false;
        td->nctors = d->n;
        td->ctors = xalloc(sizeof(Ctor) * (u64)(d->n + 1));
        for (int c = 0; c < d->n; c++) {
          td->ctors[c].name = d->list[c]->name;
          if (d->list[c]->n) boxed = true;
          CtorRef *cr = xalloc(sizeof *cr);
          cr->td = td;
          cr->tag = c;
          map_put(&ctors, fmt("%s.%s", d->name, d->list[c]->name), cr);
        }
        t->kind = boxed ? K_IND : K_ENUM;
      }
      map_put(&typedecls, d->name, td);
      break;
    }
    case N_ALIAS: {
      Alias *al = xalloc(sizeof *al);
      al->node = d;
      map_put(&aliases, d->name, al);
      break;
    }
    case N_DEF: {
      bool io = d->type && d->type->kind == N_TYNAME && d->type->name == S("IO");
      if (d->n == 0 && !d->str && !io) {
        if (map_get(&globals, d->name)) error_at(d, "duplicate definition '%s'", d->name);
        Global *g = xalloc(sizeof *g);
        g->name = d->name;
        g->node = d;
        g->index = -1;
        map_put(&globals, d->name, g);
      } else {
        if (map_get(&funcs, d->name)) error_at(d, "duplicate definition '%s'", d->name);
        Func *f = xalloc(sizeof *f);
        f->name = d->name;
        f->node = d;
        f->ext = d->str;
        map_put(&funcs, d->name, f);
      }
      break;
    }
    }
  }
}

static const struct {
  const char *sym;
  int id;
} intrinsics[] = {
    {"leanc_syscall", IN_SYSCALL}, {"leanc_load8", IN_LOAD8},     {"leanc_load16", IN_LOAD16},
    {"leanc_load32", IN_LOAD32},   {"leanc_load64", IN_LOAD64},   {"leanc_store8", IN_STORE8},
    {"leanc_store16", IN_STORE16}, {"leanc_store32", IN_STORE32}, {"leanc_store64", IN_STORE64},
    {"leanc_copy", IN_COPY},       {"leanc_fill", IN_FILL},       {"leanc_memeq", IN_MEMEQ},
    {"leanc_cas32", IN_CAS32},     {"leanc_cas64", IN_CAS64},     {"leanc_xadd64", IN_XADD64},
    {"leanc_xchg32", IN_XCHG32},   {"leanc_pause", IN_PAUSE},     {"leanc_rdtsc", IN_RDTSC},
    {"leanc_ptr", IN_PTR},         {"leanc_ofptr", IN_OFPTR},     {"leanc_forget", IN_DROPPED},
    {NULL, 0}};

static void resolve_sig(Func *f) {
  if (f->sig_done) return;
  f->sig_done = true;
  Node *d = f->node;
  f->nparams = d->n;
  f->ptypes = xalloc(sizeof(Type *) * (u64)(d->n + 1));
  f->pnames = xalloc(sizeof(char *) * (u64)(d->n + 1));
  for (int i = 0; i < d->n; i++) {
    f->ptypes[i] = resolve_type(d->list[i]->type, d, false);
    f->pnames[i] = d->list[i]->name;
  }
  if (!d->type) error_at(d, "'%s' needs an explicit return type", f->name);
  f->ret = resolve_type(d->type, d, true);
  if (f->ext) {
    for (int i = 0; intrinsics[i].sym; i++)
      if (f->ext == S(intrinsics[i].sym)) f->intrin = intrinsics[i].id;
    if (!f->intrin) error_at(d, "unknown extern \"%s\": leanc only links its own leanc_* intrinsics", f->ext);
  }
}

Func *elab_find_func(const char *name) { return map_get(&funcs, intern(name)); }

static void queue(Func *f) {
  if (f->queued) return;
  f->queued = true;
  resolve_sig(f);
  if (f->intrin) return;
  if (nwork == capwork) {
    int cap = capwork ? capwork * 2 : 64;
    Func **n = xalloc(sizeof(Func *) * (u64)cap);
    memcpy(n, work, sizeof(Func *) * (u64)nwork);
    work = n;
    capwork = cap;
  }
  work[nwork++] = f;
}

Func *elab_require(const char *name) {
  Func *f = elab_find_func(name);
  if (!f) fatal("runtime function '%s' is missing (is rt/Rt.lean on the include path?)", name);
  queue(f);
  return f;
}

// ---------------------------------------------------------------- builtins
enum { B_OP = 1, B_RT, B_CAST, B_SPECIAL };
enum {
  SP_TOSTRING = 1, SP_MIN, SP_MAX, SP_PURE, SP_IDRUN, SP_PANIC, SP_UNREACHABLE, SP_PRINT, SP_SOME, SP_NONE,
  SP_TRUE, SP_FALSE, SP_NOT, SP_UNIT, SP_ARRAY_STATIC, SP_ARRAY_METHOD, SP_OPTION_METHOD, SP_CONV, SP_EXIT,
  SP_DECIDE,
};

typedef struct {
  const char *name;
  const char *sig; // param codes, '&' marks borrowed, '>' result
  int kind;
  int arg;
  const char *rt;
  Type *conv_to;   // SP_CONV
} Builtin;

static Builtin builtins[] = {
    {"ByteArray.empty", ">Y", B_RT, 0, "Rt.baEmpty"},
    {"ByteArray.emptyWithCapacity", "N>Y", B_RT, 0, "Rt.baNew"},
    {"ByteArray.mkEmpty", "N>Y", B_RT, 0, "Rt.baNew"},
    {"ByteArray.push", "Yb>Y", B_OP, OP_BA_PUSH},
    {"ByteArray.size", "Y&>N", B_OP, OP_BA_SIZE},
    {"ByteArray.get!", "Y&N>b", B_OP, OP_BA_GET},
    {"ByteArray.set!", "YNb>Y", B_OP, OP_BA_SET},
    {"ByteArray.extract", "Y&NN>Y", B_RT, 0, "Rt.baExtract"},
    {"ByteArray.append", "YY&>Y", B_RT, 0, "Rt.baAppend"},
    {"ByteArray.isEmpty", "Y&>B", B_RT, 0, "Rt.baIsEmpty"},
    {"ByteArray.copySlice", "Y&NYNN>Y", B_RT, 0, "Rt.baCopySlice"},
    {"String.append", "SS&>S", B_RT, 0, "Rt.baAppend"},
    {"String.length", "S&>N", B_RT, 0, "Rt.strLength"},
    {"String.utf8ByteSize", "S&>N", B_OP, OP_BA_SIZE},
    {"String.toUTF8", "S>Y", B_CAST},
    {"String.fromUTF8!", "Y>S", B_CAST},
    {"String.push", "Sc>S", B_RT, 0, "Rt.strPush"},
    {"String.singleton", "c>S", B_RT, 0, "Rt.strSingleton"},
    {"String.isEmpty", "S&>B", B_RT, 0, "Rt.baIsEmpty"},
    {"String.toNat!", "S&>N", B_RT, 0, "Rt.strToNat"},
    {"IO.sleep", "d>U", B_RT, 0, "Rt.sleepMs"},
    {"IO.monoMsNow", ">N", B_RT, 0, "Rt.monoMs"},
    {"IO.monoNanosNow", ">N", B_RT, 0, "Rt.monoNs"},
    {"IO.getRandomBytes", "z>Y", B_RT, 0, "Rt.randomBytes"},
    {"IO.Process.exit", "b>!", B_RT, 0, "Rt.exit"},
    {"IO.println", "", B_SPECIAL, SP_PRINT, "Rt.println"},
    {"IO.print", "", B_SPECIAL, SP_PRINT, "Rt.print"},
    {"IO.eprintln", "", B_SPECIAL, SP_PRINT, "Rt.eprintln"},
    {"IO.eprint", "", B_SPECIAL, SP_PRINT, "Rt.eprint"},
    {"toString", "", B_SPECIAL, SP_TOSTRING},
    {"min", "", B_SPECIAL, SP_MIN},
    {"max", "", B_SPECIAL, SP_MAX},
    {"pure", "", B_SPECIAL, SP_PURE},
    {"Id.run", "", B_SPECIAL, SP_IDRUN},
    {"panic!", "", B_SPECIAL, SP_PANIC},
    {"unreachable!", "", B_SPECIAL, SP_UNREACHABLE},
    {"some", "", B_SPECIAL, SP_SOME},
    {"Option.some", "", B_SPECIAL, SP_SOME},
    {"none", "", B_SPECIAL, SP_NONE},
    {"Option.none", "", B_SPECIAL, SP_NONE},
    {"true", "", B_SPECIAL, SP_TRUE},
    {"Bool.true", "", B_SPECIAL, SP_TRUE},
    {"false", "", B_SPECIAL, SP_FALSE},
    {"Bool.false", "", B_SPECIAL, SP_FALSE},
    {"not", "", B_SPECIAL, SP_NOT},
    {"Bool.not", "", B_SPECIAL, SP_NOT},
    {"decide", "", B_SPECIAL, SP_DECIDE},
    {"Unit.unit", "", B_SPECIAL, SP_UNIT},
    {"Array.empty", "", B_SPECIAL, SP_ARRAY_STATIC, "empty"},
    {"Array.emptyWithCapacity", "", B_SPECIAL, SP_ARRAY_STATIC, "cap"},
    {"Array.mkEmpty", "", B_SPECIAL, SP_ARRAY_STATIC, "cap"},
    {"Array.replicate", "", B_SPECIAL, SP_ARRAY_STATIC, "replicate"},
    {"Array.mkArray", "", B_SPECIAL, SP_ARRAY_STATIC, "replicate"},
    {NULL}};

static Type *int_type_named(const char *s, int n) {
  static const char *names[] = {"Nat", "UInt8", "UInt16", "UInt32", "UInt64", "USize", "Char"};
  Type *types[] = {ty_nat, ty_u8, ty_u16, ty_u32, ty_u64, ty_usize, ty_char};
  for (int i = 0; i < 7; i++)
    if ((int)strlen(names[i]) == n && memcmp(names[i], s, (unsigned long)n) == 0) return types[i];
  return NULL;
}

static Map builtin_map;
static Map dyn_builtins;

// Numeric conversions (UInt8.toNat, Nat.toUInt64, UInt32.ofNat, Char.ofNat, ...)
// are recognised by shape instead of being listed one by one.
static Builtin *lookup_builtin(const char *name) {
  Builtin *b = map_get(&builtin_map, name);
  if (b) return b;
  b = map_get(&dyn_builtins, name);
  if (b) return b;
  const char *dot = str_rchr(name, '.');
  if (!dot) return NULL;
  Type *src = int_type_named(name, (int)(dot - name));
  if (!src) return NULL;
  Type *from = NULL, *to = NULL;
  const char *m = dot + 1;
  if (str_starts(m, "to")) {
    from = src;
    to = int_type_named(m + 2, (int)strlen(m + 2));
  } else if (m == NULL || (m[0] == 'o' && m[1] == 'f' && m[2] == 'N' && m[3] == 'a' && m[4] == 't' && !m[5])) {
    from = ty_nat;
    to = src;
  }
  if (!to || !from) return NULL;
  b = xalloc(sizeof *b);
  b->name = name;
  b->kind = B_SPECIAL;
  b->arg = SP_CONV;
  b->conv_to = to;
  b->sig = (const char *)from; // source type smuggled through sig
  map_put(&dyn_builtins, name, b);
  return b;
}

void elab_init(void) {
  for (int i = 0; builtins[i].name; i++) map_put(&builtin_map, intern(builtins[i].name), &builtins[i]);
}

static Type *sig_type(char c) {
  switch (c) {
  case 'N': return ty_nat;
  case 'b': return ty_u8;
  case 'w': return ty_u16;
  case 'd': return ty_u32;
  case 'q': return ty_u64;
  case 'z': return ty_usize;
  case 'B': return ty_bool;
  case 'c': return ty_char;
  case 'S': return ty_string;
  case 'Y': return ty_bytes;
  case 'U': return ty_unit;
  case '!': return ty_never;
  }
  fatal("bad builtin signature char '%c'", c);
}

// ------------------------------------------------------------ name lookup
enum { R_NONE, R_FUNC, R_GLOBAL, R_CTOR, R_BUILTIN };
typedef struct {
  int kind;
  Func *fn;
  Global *glob;
  CtorRef *ctor;
  Builtin *bi;
} Ref;

static Ref ref_tmp;
static void *try_ref(const char *full) {
  Ref r = {0};
  if ((r.fn = map_get(&funcs, full))) r.kind = R_FUNC;
  else if ((r.glob = map_get(&globals, full))) r.kind = R_GLOBAL;
  else if ((r.ctor = map_get(&ctors, full))) r.kind = R_CTOR;
  else if ((r.bi = lookup_builtin(full))) r.kind = R_BUILTIN;
  else return NULL;
  ref_tmp = r;
  return &ref_tmp;
}

static Ref resolve_ref(const char *name, Node *ctx) {
  Ref none = {0};
  Ref *r = resolve_scoped(name, ctx, try_ref);
  return r ? *r : none;
}

// ----------------------------------------------------------- expressions
static Expr *elab(Node *n, Type *expected);
static Expr *elab_stmts(Node **list, int n, Type *expected, bool tail, Node *at);
static Expr *elab_app(Node *head, Node **args, int nargs, Type *expected, Node *at);
static Expr *apply_method(Expr *recv, const char *name, Node **args, int nargs, Type *expected, Node *at);

static Expr *rtcall(const char *rt, const char *own, Type *ret, Node *at, int n, Expr *a, Expr *b, Expr *c) {
  Expr *e = mk_op(OP_RTCALL, ret, at, n, a, b, c);
  e->fn = elab_require(rt);
  e->own = own;
  return e;
}

static Expr *conv(Expr *e, Type *to, Node *at) {
  if (ty_eq(e->type, to)) return e;
  if (e->kind == E_INT && ty_bits(to) >= ty_bits(e->type)) return mk_int(e->num, to, at);
  return mk_op(OP_CONV, to, at, 1, e, NULL, NULL);
}

static Expr *to_string(Expr *e, Node *at) {
  Type *t = ty_strip(e->type);
  if (t == ty_string) return e;
  if (ty_is_int(t)) return rtcall("Rt.natToString", "o", ty_string, at, 1, conv(e, ty_u64, at), NULL, NULL);
  if (t == ty_bool) return rtcall("Rt.boolToString", "o", ty_string, at, 1, e, NULL, NULL);
  if (t == ty_char) return rtcall("Rt.strSingleton", "o", ty_string, at, 1, e, NULL, NULL);
  error_at(at, "no string conversion for type %s", ty_name(t));
}

static Expr *str_append(Expr *a, Expr *b, Node *at) {
  return rtcall("Rt.baAppend", "ob", a->type, at, 2, a, b, NULL);
}

static bool is_literalish(Node *n) {
  if (n->kind == N_NUM) return true;
  if (n->kind == N_UNOP && n->name != S("!")) return is_literalish(n->a);
  if (n->kind == N_BINOP) {
    const char *o = n->name;
    if (o == S("+") || o == S("-") || o == S("*") || o == S("/") || o == S("%") || o == S("<<<") ||
        o == S(">>>") || o == S("&&&") || o == S("|||") || o == S("^^^"))
      return is_literalish(n->a) && is_literalish(n->b);
  }
  return false;
}

static Expr *elab_binop(Node *n, Type *expected) {
  const char *o = n->name;
  if (o == S("&&") || o == S("∧") || o == S("||") || o == S("∨")) {
    Expr *a = elab(n->a, ty_bool), *b = elab(n->b, ty_bool);
    check_type(a, ty_bool, n->a);
    check_type(b, ty_bool, n->b);
    Expr *e = mke(E_IF, ty_bool, n);
    e->a = a;
    bool is_and = o == S("&&") || o == S("∧");
    e->b = is_and ? b : mk_int(1, ty_bool, n);
    e->c = is_and ? mk_int(0, ty_bool, n) : b;
    return e;
  }
  int op = 0;
  bool cmp = false;
  if (o == S("+")) op = OP_ADD;
  else if (o == S("-")) op = OP_SUB;
  else if (o == S("*")) op = OP_MUL;
  else if (o == S("/")) op = OP_DIV;
  else if (o == S("%")) op = OP_MOD;
  else if (o == S("&&&")) op = OP_AND;
  else if (o == S("|||")) op = OP_OR;
  else if (o == S("^^^")) op = OP_XOR;
  else if (o == S("<<<")) op = OP_SHL;
  else if (o == S(">>>")) op = OP_SHR;
  else if (o == S("==") || o == S("=")) op = OP_EQ, cmp = true;
  else if (o == S("!=") || o == S("≠")) op = OP_NE, cmp = true;
  else if (o == S("<")) op = OP_LT, cmp = true;
  else if (o == S("<=") || o == S("≤")) op = OP_LE, cmp = true;
  else if (o == S(">")) op = OP_GT, cmp = true;
  else if (o == S(">=") || o == S("≥")) op = OP_GE, cmp = true;

  Type *want = NULL;
  if (!cmp && expected && (ty_is_int(expected) || ty_strip(expected) == ty_string || ty_strip(expected) == ty_bytes))
    want = ty_strip(expected);
  Expr *a, *b;
  if (is_literalish(n->a) && !want) {
    b = elab(n->b, NULL);
    a = elab(n->a, b->type);
  } else {
    a = elab(n->a, want);
    b = elab(n->b, a->type);
  }
  Type *t = ty_strip(a->type);
  if (ty_strip(a->type)->kind == K_NEVER) t = ty_strip(b->type);
  check_type(b, t, n->b);

  if (o == S("++")) {
    if (t != ty_string && t != ty_bytes) error_at(n, "'++' is only supported on String and ByteArray, not %s", ty_name(t));
    return str_append(a, b, n);
  }
  if (!op) error_at(n, "unsupported operator '%s'", o);
  if (cmp) {
    bool eq = op == OP_EQ || op == OP_NE;
    if (eq && (t == ty_string || t == ty_bytes)) {
      Expr *e = rtcall("Rt.baEq", "bb", ty_bool, n, 2, a, b, NULL);
      return op == OP_EQ ? e : mk_op(OP_LNOT, ty_bool, n, 1, e, NULL, NULL);
    }
    bool scalar = !ty_is_ptr(t) && t->kind != K_NEVER;
    if (!scalar || (!eq && !ty_is_int(t) && t != ty_char))
      error_at(n, "operator '%s' is not supported on type %s", o, ty_name(t));
    return mk_op(op, ty_bool, n, 2, a, b, NULL);
  }
  if (!ty_is_int(t)) error_at(n, "operator '%s' needs an integer type, got %s", o, ty_name(t));
  return mk_op(op, t, n, 2, a, b, NULL);
}

// ---- patterns
static Pat *mkpat(int kind, Type *t) {
  Pat *p = xalloc(sizeof *p);
  p->kind = kind;
  p->type = t;
  return p;
}

static Pat *elab_pat(Node *n, Type *t);

static Pat *ctor_pat(Type *t, int tag, Node **sub, int nsub, Node *at) {
  if (!ty_is_ptr(t)) { // enum / Bool
    if (nsub) error_at(at, "constructor takes no arguments");
    Pat *p = mkpat(P_INT, t);
    p->num = (u64)tag;
    return p;
  }
  int nf = ty_ctor_nfields(t, tag);
  if (nsub != nf) error_at(at, "constructor pattern has %d arguments, expected %d", nsub, nf);
  Pat *p = mkpat(P_CTOR, t);
  p->num = (u64)tag;
  p->nsub = nf;
  p->sub = xalloc(sizeof(Pat *) * (u64)(nf + 1));
  for (int i = 0; i < nf; i++) p->sub[i] = elab_pat(sub[i], ty_ctor_field(t, tag, i));
  return p;
}

static int find_ctor(Type *t, const char *name) {
  t = ty_strip(t);
  if (t->kind == K_OPTION) return name == S("none") ? 0 : name == S("some") ? 1 : -1;
  if (t->kind == K_BOOL) return name == S("false") ? 0 : name == S("true") ? 1 : -1;
  if (t->kind == K_PROD) return name == S("mk") ? 0 : -1;
  if (t->kind == K_STRUCT || t->kind == K_IND || t->kind == K_ENUM) {
    resolve_decl(t->decl);
    for (int i = 0; i < t->decl->nctors; i++)
      if (t->decl->ctors[i].name == name) return i;
  }
  return -1;
}

// Resolves an identifier in pattern position to a constructor tag of t, or -1.
static int pat_ctor(const char *name, Type *t) {
  const char *dot = str_rchr(name, '.');
  const char *shortname = dot ? intern(dot + 1) : name;
  int tag = find_ctor(t, shortname);
  if (tag < 0) return -1;
  if (!dot) {
    // bare name: must actually resolve to this constructor in scope
    if (t->kind == K_OPTION || t->kind == K_BOOL) return tag;
    Ref r = resolve_ref(name, cx->decl);
    if (r.kind == R_CTOR && r.ctor->td->type == t && r.ctor->tag == tag) return tag;
    return -1;
  }
  return tag;
}

static Pat *tuple_pat(Node **items, int n, Type *t, Node *at) {
  t = ty_strip(t);
  if (n == 1) return elab_pat(items[0], t);
  if (t->kind != K_PROD) error_at(at, "tuple pattern used with non-tuple type %s", ty_name(t));
  Pat *p = mkpat(P_CTOR, t);
  p->nsub = 2;
  p->sub = xalloc(sizeof(Pat *) * 2);
  p->sub[0] = elab_pat(items[0], t->a);
  p->sub[1] = tuple_pat(items + 1, n - 1, t->b, at);
  return p;
}

static Pat *elab_pat(Node *n, Type *t) {
  t = ty_strip(t);
  switch (n->kind) {
  case N_IDENT: {
    if (n->name == S("_")) return mkpat(P_WILD, t);
    int tag = pat_ctor(n->name, t);
    if (tag >= 0) return ctor_pat(t, tag, NULL, 0, n);
    if (str_rchr(n->name, '.')) error_at(n, "unknown constructor '%s' for type %s", n->name, ty_name(t));
    Pat *p = mkpat(P_VAR, t);
    p->var = new_var(n->name, t, false);
    bind(p->var, n);
    return p;
  }
  case N_DOTID: {
    int tag = find_ctor(t, n->name);
    if (tag < 0) error_at(n, "type %s has no constructor '%s'", ty_name(t), n->name);
    return ctor_pat(t, tag, NULL, 0, n);
  }
  case N_APP: {
    int tag = -1;
    if (n->a->kind == N_IDENT) tag = pat_ctor(n->a->name, t);
    else if (n->a->kind == N_DOTID) tag = find_ctor(t, n->a->name);
    if (tag < 0) error_at(n, "unknown constructor in pattern for type %s", ty_name(t));
    return ctor_pat(t, tag, n->list, n->n, n);
  }
  case N_NUM:
  case N_CHAR: {
    if (!ty_is_int(t) && t != ty_char) error_at(n, "literal pattern used with type %s", ty_name(t));
    Pat *p = mkpat(P_INT, t);
    p->num = n->num;
    return p;
  }
  case N_TUPLE: return tuple_pat(n->list, n->n, t, n);
  case N_ANON: {
    if (t->kind == K_PROD) return tuple_pat(n->list, n->n, t, n);
    if (t->kind != K_STRUCT) error_at(n, "anonymous constructor pattern needs a structure type, got %s", ty_name(t));
    resolve_decl(t->decl);
    return ctor_pat(t, 0, n->list, n->n, n);
  }
  }
  error_at(n, "unsupported pattern");
}

static bool pat_irrefutable(Pat *p) {
  if (p->kind == P_INT) return false;
  if (p->kind == P_CTOR) {
    if (ty_nctors(p->type) != 1) return false;
    for (int i = 0; i < p->nsub; i++)
      if (!pat_irrefutable(p->sub[i])) return false;
  }
  return true;
}

// match over already-evaluated scrutinees; `body_fn` elaborates each arm body.
typedef Expr *(*BodyFn)(Node *body, Type *expected, void *arg);

static Expr *elab_match_core(Node *at, Expr **scruts, int ns, Node **arms, int narms, Type *expected, BodyFn body_fn,
                             void *arg) {
  // bind scrutinees to hidden variables
  Var **hv = xalloc(sizeof(Var *) * (u64)(ns + 1));
  Expr *m = mke(E_MATCH, expected, at);
  m->nargs = ns;
  m->args = xalloc(sizeof(Expr *) * (u64)(ns + 1));
  for (int i = 0; i < ns; i++) {
    hv[i] = new_var(NULL, scruts[i]->type, false);
    m->args[i] = mk_local(hv[i], at);
  }
  m->narms = narms;
  m->arms = xalloc(sizeof(Arm) * (u64)(narms + 1));
  Type *result = expected ? ty_strip(expected) : NULL;
  for (int a = 0; a < narms; a++) {
    Node *an = arms[a];
    if (an->n != ns) error_at(an, "match arm has %d patterns but there are %d scrutinees", an->n, ns);
    int mark = cx->nscope;
    m->arms[a].npats = ns;
    m->arms[a].pats = xalloc(sizeof(Pat *) * (u64)(ns + 1));
    for (int i = 0; i < ns; i++) m->arms[a].pats[i] = elab_pat(an->list[i], scruts[i]->type);
    Expr *body = body_fn(an->a, result, arg);
    if (!result && ty_strip(body->type)->kind != K_NEVER) result = ty_strip(body->type);
    check_type(body, result, an->a);
    m->arms[a].body = body;
    cx->nscope = mark;
  }
  m->type = result ? result : ty_never;
  Expr *e = m;
  for (int i = ns - 1; i >= 0; i--) e = mk_let(hv[i], scruts[i], e, at);
  return e;
}

static Expr *term_body(Node *body, Type *expected, void *arg) {
  (void)arg;
  return elab(body, expected);
}

typedef struct {
  bool tail;
} StmtArg;
static Expr *stmt_body(Node *body, Type *expected, void *arg) {
  StmtArg *sa = arg;
  if (body->kind == N_DO) return elab_stmts(body->list, body->n, expected, sa->tail, body);
  return elab(body, expected);
}

static Expr *elab_match(Node *n, Type *expected, BodyFn fn, void *arg) {
  Expr **scruts = xalloc(sizeof(Expr *) * (u64)(n->n + 1));
  for (int i = 0; i < n->n; i++) scruts[i] = elab(n->list[i], NULL);
  return elab_match_core(n, scruts, n->n, n->list2, n->n2, expected, fn, arg);
}

// ---- constructors and structure instances
static Expr *mk_ctor(Type *t, int tag, Expr **args, int n, Node *at) {
  if (!ty_is_ptr(t)) return mk_int((u64)tag, t, at);
  Expr *e = mke(E_CTOR, t, at);
  e->num = (u64)tag;
  e->args = args;
  e->nargs = n;
  return e;
}

static Expr *elab_arg(Node *n, Type *want) {
  Expr *e = elab(n, want);
  check_type(e, want, n);
  if (e->type->io) error_at(n, "an IO action cannot be passed as a value here; bind its result with ← first");
  return e;
}

static Expr *elab_ctor_app(Type *t, int tag, Node **args, int nargs, Node *at) {
  int nf = ty_ctor_nfields(t, tag);
  if (nargs != nf) error_at(at, "constructor expects %d arguments, got %d", nf, nargs);
  Expr **ea = xalloc(sizeof(Expr *) * (u64)(nf + 1));
  for (int i = 0; i < nf; i++) ea[i] = elab_arg(args[i], ty_ctor_field(t, tag, i));
  return mk_ctor(t, tag, ea, nf, at);
}

static Expr *elab_tuple(Node **items, int n, Type *expected, Node *at) {
  if (n == 1) return elab(items[0], expected);
  Type *t = expected ? ty_strip(expected) : NULL;
  if (t && t->kind != K_PROD) error_at(at, "tuple used where %s is expected", ty_name(t));
  Expr **ea = xalloc(sizeof(Expr *) * 2);
  ea[0] = elab_arg(items[0], t ? t->a : NULL);
  ea[1] = elab_tuple(items + 1, n - 1, t ? t->b : NULL, at);
  if (t) check_type(ea[1], t->b, at);
  return mk_ctor(ty_prod(ty_strip(ea[0]->type), ty_strip(ea[1]->type)), 0, ea, 2, at);
}

// Elaborates a field default in the context of the structure declaration:
// its namespace, and none of the caller's local variables.
static Expr *elab_in_decl(Node *expr, Type *want, Node *decl) {
  Node *save = cx->decl;
  int nscope = cx->nscope;
  cx->decl = decl;
  cx->nscope = 0;
  Expr *e = elab_arg(expr, want);
  cx->nscope = nscope;
  cx->decl = save;
  return e;
}

static Expr *elab_struct(Node *n, Type *expected) {
  Expr *base = NULL;
  Type *t = expected ? ty_strip(expected) : NULL;
  if (n->a) {
    base = elab(n->a, t);
    t = ty_strip(base->type);
  }
  if (!t || t->kind != K_STRUCT)
    error_at(n, "structure instance needs a known structure type%s", t ? fmt(", got %s", ty_name(t)) : "");
  resolve_decl(t->decl);
  Ctor *c = &t->decl->ctors[0];
  Expr **vals = xalloc(sizeof(Expr *) * (u64)(c->nfields + 1));
  for (int i = 0; i < n->n; i++) {
    Node *f = n->list[i];
    int idx = -1;
    for (int k = 0; k < c->nfields; k++)
      if (c->fields[k].name == f->name) idx = k;
    if (idx < 0) error_at(f, "structure %s has no field '%s'", t->decl->name, f->name);
    if (vals[idx]) error_at(f, "field '%s' given twice", f->name);
    vals[idx] = elab_arg(f->a, c->fields[idx].type);
  }
  if (base) {
    Expr *e = mke(E_UPDATE, t, n);
    e->a = base;
    e->args = xalloc(sizeof(Expr *) * (u64)(n->n + 1));
    e->fields = xalloc(sizeof(int) * (u64)(n->n + 1));
    for (int k = 0; k < c->nfields; k++)
      if (vals[k]) {
        e->fields[e->nargs] = k;
        e->args[e->nargs++] = vals[k];
      }
    return e;
  }
  for (int k = 0; k < c->nfields; k++)
    if (!vals[k]) {
      if (!c->fields[k].dflt) error_at(n, "missing field '%s' of structure %s", c->fields[k].name, t->decl->name);
      vals[k] = elab_in_decl(c->fields[k].dflt, c->fields[k].type, t->decl->node);
    }
  return mk_ctor(t, 0, vals, c->nfields, n);
}

// ---- calls
static Expr *call_func(Func *f, Expr *first, Node **args, int nargs, Node *at) {
  resolve_sig(f);
  int total = nargs + (first ? 1 : 0);
  if (total != f->nparams)
    error_at(at, "'%s' expects %d arguments, got %d (partial application is not supported)", f->name, f->nparams,
             total);
  Expr **ea = xalloc(sizeof(Expr *) * (u64)(total + 1));
  int k = 0;
  if (first) {
    check_type(first, f->ptypes[0], at);
    ea[k++] = first;
  }
  for (int i = 0; i < nargs; i++, k++) ea[k] = elab_arg(args[i], f->ptypes[k]);
  if (f->intrin) {
    Expr *e = mke(E_OP, f->ret, at);
    e->num = OP_INTRIN;
    e->num2 = (u64)f->intrin;
    e->args = ea;
    e->nargs = total;
    return e;
  }
  queue(f);
  Expr *e = mke(E_CALL, f->ret, at);
  e->fn = f;
  e->args = ea;
  e->nargs = total;
  return e;
}

static Expr *array_static(const char *which, Node **args, int nargs, Type *expected, Node *at) {
  Type *t = expected ? ty_strip(expected) : NULL;
  if (which == S("replicate")) {
    if (nargs != 2) error_at(at, "Array.replicate expects 2 arguments");
    Expr *n = elab_arg(args[0], ty_nat);
    Expr *v = elab_arg(args[1], t && t->kind == K_ARRAY ? t->elem : NULL);
    return mk_op(OP_ARR_REPLICATE, ty_array(ty_strip(v->type)), at, 2, n, v, NULL);
  }
  if (!t || t->kind != K_ARRAY) error_at(at, "cannot infer the element type of this empty array; add a type annotation");
  Expr *cap = which == S("cap") ? (nargs == 1 ? elab_arg(args[0], ty_nat) : NULL) : mk_int(0, ty_nat, at);
  if (!cap || (which == S("empty") && nargs)) error_at(at, "wrong number of arguments");
  return mk_op(OP_ARR_EMPTY, t, at, 1, cap, NULL, NULL);
}

static Expr *apply_builtin(Builtin *b, Expr *first, Node **args, int nargs, Type *expected, Node *at) {
  int total = nargs + (first ? 1 : 0);
  if (b->kind == B_SPECIAL) {
    // gather the (single) argument for one-argument specials
    Expr *one = NULL;
#define ONE(want)                                                                                                      \
  do {                                                                                                                 \
    if (total != 1) error_at(at, "'%s' expects 1 argument", b->name);                                                  \
    one = first ? first : elab(args[0], want);                                                                         \
  } while (0)
    switch (b->arg) {
    case SP_TRUE: case SP_FALSE:
      if (total) error_at(at, "Bool constant applied to arguments");
      return mk_int(b->arg == SP_TRUE, ty_bool, at);
    case SP_UNIT: return mk_unit(at);
    case SP_NOT:
      ONE(ty_bool);
      check_type(one, ty_bool, at);
      return mk_op(OP_LNOT, ty_bool, at, 1, one, NULL, NULL);
    case SP_DECIDE:
      ONE(ty_bool);
      return one;
    case SP_PURE:
      if (total == 0) return mk_unit(at);
      ONE(expected);
      return one;
    case SP_IDRUN:
      ONE(expected);
      return one;
    case SP_TOSTRING:
      ONE(NULL);
      return to_string(one, at);
    case SP_PRINT: {
      ONE(NULL);
      return rtcall(b->rt, "b", ty_io(ty_unit), at, 1, to_string(one, at), NULL, NULL);
    }
    case SP_PANIC: {
      ONE(ty_string);
      check_type(one, ty_string, at);
      Expr *e = mk_op(OP_PANIC, ty_never, at, 1, one, NULL, NULL);
      e->fn = elab_require("Rt.panicMsg");
      return e;
    }
    case SP_UNREACHABLE: {
      Expr *msg = mke(E_STR, ty_string, at);
      msg->num = (u64)intern_strlit("unreachable code reached", 24);
      Expr *e = mk_op(OP_PANIC, ty_never, at, 1, msg, NULL, NULL);
      e->fn = elab_require("Rt.panicMsg");
      return e;
    }
    case SP_SOME: {
      Type *t = expected ? ty_strip(expected) : NULL;
      ONE(t && t->kind == K_OPTION ? t->elem : NULL);
      Expr **ea = xalloc(sizeof(Expr *));
      ea[0] = one;
      return mk_ctor(ty_option(ty_strip(one->type)), 1, ea, 1, at);
    }
    case SP_NONE: {
      Type *t = expected ? ty_strip(expected) : NULL;
      if (!t || t->kind != K_OPTION) error_at(at, "cannot infer the type of 'none'; add a type annotation");
      return mk_ctor(t, 0, NULL, 0, at);
    }
    case SP_MIN: case SP_MAX: {
      if (total != 2 || first) error_at(at, "'%s' expects 2 arguments", b->name);
      Expr *x = elab(args[0], expected), *y = elab(args[1], x->type);
      check_type(y, x->type, at);
      if (!ty_is_int(x->type)) error_at(at, "min/max need integer arguments");
      // bind both to temporaries so each is evaluated once
      Var *vx = new_var(NULL, x->type, false), *vy = new_var(NULL, y->type, false);
      Expr *c = mk_op(OP_LE, ty_bool, at, 2, mk_local(vx, at), mk_local(vy, at), NULL);
      Expr *sel = mke(E_IF, ty_strip(x->type), at);
      sel->a = c;
      sel->b = mk_local(b->arg == SP_MIN ? vx : vy, at);
      sel->c = mk_local(b->arg == SP_MIN ? vy : vx, at);
      return mk_let(vx, x, mk_let(vy, y, sel, at), at);
    }
    case SP_CONV: {
      Type *from = (Type *)b->sig;
      ONE(from);
      check_type(one, from, at);
      return conv(one, b->conv_to, at);
    }
    case SP_ARRAY_STATIC:
      if (first) error_at(at, "unexpected receiver");
      return array_static(S(b->rt), args, nargs, expected, at);
    }
    error_at(at, "internal: unhandled builtin '%s'", b->name);
  }

  // signature-driven builtins
  const char *s = b->sig;
  Expr *ea[8] = {0};
  char own[9] = {0};
  int k = 0;
  for (; *s && *s != '>'; s++) {
    if (*s == '&') continue;
    if (k >= total) error_at(at, "'%s': too few arguments", b->name);
    Type *want = sig_type(*s);
    if (k == 0 && first) {
      check_type(first, want, at);
      ea[k] = first;
    } else {
      ea[k] = elab_arg(args[k - (first ? 1 : 0)], want);
    }
    own[k] = s[1] == '&' ? 'b' : 'o';
    k++;
  }
  if (k != total) error_at(at, "'%s' expects %d arguments, got %d", b->name, k, total);
  Type *ret = sig_type(s[1]);
  // IO builtins: everything under IO.*
  if (str_starts(b->name, "IO.")) ret = ty_io(ret);
  if (b->kind == B_CAST) {
    Expr *e = mk_op(OP_CAST, ret, at, 1, ea[0], NULL, NULL);
    return e;
  }
  Expr *e = mke(E_OP, ret, at);
  e->nargs = k;
  e->args = xalloc(sizeof(Expr *) * (u64)(k + 1));
  for (int i = 0; i < k; i++) e->args[i] = ea[i];
  if (b->kind == B_OP) {
    e->num = (u64)b->arg;
  } else {
    e->num = OP_RTCALL;
    e->fn = elab_require(b->rt);
    e->own = intern(own);
  }
  return e;
}

static Expr *apply_ref(Ref r, const char *name, Expr *first, Node **args, int nargs, Type *expected, Node *at) {
  switch (r.kind) {
  case R_FUNC: return call_func(r.fn, first, args, nargs, at);
  case R_BUILTIN: return apply_builtin(r.bi, first, args, nargs, expected, at);
  case R_CTOR: {
    if (first) error_at(at, "constructor used as a method");
    Type *t = decl_type(r.ctor->td);
    return elab_ctor_app(t, r.ctor->tag, args, nargs, at);
  }
  case R_GLOBAL: {
    if (nargs || first) error_at(at, "'%s' is a constant and cannot be applied", name);
    elab_global(r.glob);
    if (r.glob->init->kind == E_INT) return mk_int(r.glob->init->num, r.glob->type, at);
    Expr *e = mke(E_GLOBAL, r.glob->type, at);
    e->glob = r.glob;
    return e;
  }
  }
  error_at(at, "unknown identifier '%s'", name);
}

static Expr *proj(Expr *base, int idx, Node *at) {
  Expr *e = mke(E_PROJ, ty_ctor_field(base->type, 0, idx), at);
  e->a = base;
  e->num = (u64)idx;
  return e;
}

static Expr *apply_method(Expr *recv, const char *name, Node **args, int nargs, Type *expected, Node *at) {
  Type *t = ty_strip(recv->type);
  if (recv->type->io) error_at(at, "cannot use the result of an IO action directly; bind it with ← first");
  if (t->kind == K_PROD) {
    int idx = (name == S("1") || name == S("fst")) ? 0 : (name == S("2") || name == S("snd")) ? 1 : -1;
    if (idx < 0 || nargs) error_at(at, "unknown tuple projection '.%s'", name);
    return proj(recv, idx, at);
  }
  if (t->kind == K_STRUCT) {
    resolve_decl(t->decl);
    Ctor *c = &t->decl->ctors[0];
    for (int i = 0; i < c->nfields; i++)
      if (c->fields[i].name == name) {
        if (nargs) error_at(at, "field '%s' is not a function", name);
        return proj(recv, i, at);
      }
  }
  if (t->kind == K_ARRAY) {
    if (name == S("size") && nargs == 0) return mk_op(OP_ARR_SIZE, ty_nat, at, 1, recv, NULL, NULL);
    if (name == S("push") && nargs == 1)
      return mk_op(OP_ARR_PUSH, t, at, 2, recv, elab_arg(args[0], t->elem), NULL);
    if (name == S("get!") && nargs == 1)
      return mk_op(OP_ARR_GET, t->elem, at, 2, recv, elab_arg(args[0], ty_nat), NULL);
    if (name == S("set!") && nargs == 2)
      return mk_op(OP_ARR_SET, t, at, 3, recv, elab_arg(args[0], ty_nat), elab_arg(args[1], t->elem));
    if (name == S("pop") && nargs == 0) return mk_op(OP_ARR_POP, t, at, 1, recv, NULL, NULL);
    if (name == S("isEmpty") && nargs == 0)
      return mk_op(OP_EQ, ty_bool, at, 2, mk_op(OP_ARR_SIZE, ty_nat, at, 1, recv, NULL, NULL), mk_int(0, ty_nat, at),
                   NULL);
    error_at(at, "unsupported Array method '%s' (with %d arguments)", name, nargs);
  }
  if (t->kind == K_OPTION) {
    if ((name == S("isSome") || name == S("isNone")) && nargs == 0) {
      Expr *tag = mk_op(OP_TAG, ty_nat, at, 1, recv, NULL, NULL);
      return mk_op(OP_EQ, ty_bool, at, 2, tag, mk_int(name == S("isSome"), ty_nat, at), NULL);
    }
    if (name == S("get!") && nargs == 0) return mk_op(OP_OPT_GET, t->elem, at, 1, recv, NULL, NULL);
    error_at(at, "unsupported Option method '%s'", name);
  }
  const char *full = fmt("%s.%s", type_ns(t), name);
  Ref r = {0};
  if ((r.fn = map_get(&funcs, full))) r.kind = R_FUNC;
  else if ((r.bi = lookup_builtin(full))) r.kind = R_BUILTIN;
  else error_at(at, "type %s has no field or method '%s'", ty_name(t), name);
  return apply_ref(r, full, recv, args, nargs, expected, at);
}

// Resolves a dotted identifier to an expression, applying `args` to the last
// component.
static Expr *elab_ident_app(Node *id, Node **args, int nargs, Type *expected, Node *at) {
  const char *name = id->name;
  // split into components
  const char *comp[32];
  int nc = 0;
  const char *s = name;
  for (;;) {
    const char *d = s;
    while (*d && *d != '.') d++;
    if (nc == 32) error_at(id, "identifier too long");
    comp[nc++] = intern_n(s, (int)(d - s));
    if (!*d) break;
    s = d + 1;
  }
  Expr *e = NULL;
  int used = 0;
  Var *v = find_local(comp[0]);
  if (v) {
    e = mk_local(v, id);
    used = 1;
  } else {
    for (int k = nc; k >= 1 && !e; k--) {
      const char *prefix = name;
      if (k < nc) {
        Buf b = {0};
        for (int i = 0; i < k; i++) buf_fmt(&b, i ? ".%s" : "%s", comp[i]);
        prefix = intern_n(b.p, (int)b.len);
      }
      Ref r = resolve_ref(prefix, cx->decl);
      if (r.kind == R_NONE) continue;
      if (k == nc) return apply_ref(r, name, NULL, args, nargs, expected, at);
      e = apply_ref(r, prefix, NULL, NULL, 0, NULL, at);
      used = k;
    }
    if (!e) error_at(id, "unknown identifier '%s'", name);
  }
  if (used == nc) {
    if (nargs) error_at(at, "'%s' is not a function", name);
    return e;
  }
  for (int i = used; i < nc; i++) {
    bool last = i == nc - 1;
    e = apply_method(e, comp[i], last ? args : NULL, last ? nargs : 0, last ? expected : NULL, at);
  }
  return e;
}

static Expr *elab_app(Node *head, Node **args, int nargs, Type *expected, Node *at) {
  switch (head->kind) {
  case N_IDENT: return elab_ident_app(head, args, nargs, expected, at);
  case N_FIELD: {
    Expr *recv = elab(head->a, NULL);
    return apply_method(recv, head->name, args, nargs, expected, at);
  }
  case N_DOTID: {
    Type *t = expected ? ty_strip(expected) : NULL;
    if (!t) error_at(head, "cannot resolve '.%s' without an expected type", head->name);
    int tag = find_ctor(t, head->name);
    if (tag >= 0) return elab_ctor_app(t, tag, args, nargs, at);
    const char *full = fmt("%s.%s", type_ns(t), head->name);
    Ref r = {0};
    if ((r.fn = map_get(&funcs, full))) r.kind = R_FUNC;
    else if ((r.glob = map_get(&globals, full))) r.kind = R_GLOBAL;
    else if ((r.bi = lookup_builtin(full))) r.kind = R_BUILTIN;
    else error_at(head, "type %s has no constructor or function '%s'", ty_name(t), head->name);
    return apply_ref(r, full, NULL, args, nargs, expected, at);
  }
  }
  error_at(at, "this expression cannot be applied to arguments");
}

// ---- do blocks
static Expr *seq2(Expr *a, Expr *b, Node *at) {
  Expr *e = mke(E_SEQ, b->type, at);
  int na = a->kind == E_SEQ ? a->nargs : 1, nb = b->kind == E_SEQ ? b->nargs : 1;
  e->args = xalloc(sizeof(Expr *) * (u64)(na + nb));
  if (a->kind == E_SEQ) memcpy(e->args, a->args, sizeof(Expr *) * (u64)na);
  else e->args[0] = a;
  if (b->kind == E_SEQ) memcpy(e->args + na, b->args, sizeof(Expr *) * (u64)nb);
  else e->args[na] = b;
  e->nargs = na + nb;
  return e;
}

static Expr *elab_let_init(Node *n) {
  Type *want = n->type ? resolve_type(n->type, cx->decl, false) : NULL;
  Expr *init = elab(n->b, want);
  check_type(init, want, n->b);
  if (init->type->io && !(n->flag & 2))
    error_at(n, "this is an IO action; use `let x ← ...` to run it and bind its result");
  if (ty_strip(init->type)->kind == K_NEVER && !want) error_at(n, "cannot infer the type of this binding");
  if (want && ty_strip(init->type)->kind == K_NEVER) init->type = want;
  return init;
}

// let with a destructuring pattern: body elaborated by callback while bound
static Expr *elab_let_pat(Node *n, Expr *init, Node **rest, int nrest, Type *expected, bool tail, Node *term_body) {
  int mark = cx->nscope;
  Pat *p = elab_pat(n->a, init->type);
  if (!pat_irrefutable(p)) error_at(n, "this pattern can fail; use match instead");
  Expr *body = term_body ? elab(term_body, expected) : elab_stmts(rest, nrest, expected, tail, n);
  cx->nscope = mark;
  Var *hv = new_var(NULL, init->type, false);
  Expr *m = mke(E_MATCH, body->type, n);
  m->nargs = 1;
  m->args = xalloc(sizeof(Expr *));
  m->args[0] = mk_local(hv, n);
  m->narms = 1;
  m->arms = xalloc(sizeof(Arm));
  m->arms[0].npats = 1;
  m->arms[0].pats = xalloc(sizeof(Pat *));
  m->arms[0].pats[0] = p;
  m->arms[0].body = body;
  return mk_let(hv, init, m, n);
}

static Expr *elab_for(Node *n) {
  Node *it = n->a;
  int mark = cx->nscope;
  Expr *result;
  cx->loop_depth++;
  if (it->kind == N_RANGE) {
    Expr *lo = it->a ? elab_arg(it->a, ty_nat) : mk_int(0, ty_nat, n);
    Expr *hi = elab_arg(it->b, ty_nat);
    Expr *step = it->c ? elab_arg(it->c, ty_nat) : mk_int(1, ty_nat, n);
    Var *vhi = new_var(NULL, ty_nat, false), *vi = new_var(NULL, ty_nat, true), *vstep = NULL;
    if (step->kind != E_INT) vstep = new_var(NULL, ty_nat, false);
    Var *x = new_var(n->name, ty_nat, false);
    bind(x, n);
    Expr *body = elab_stmts(n->b->list, n->b->n, ty_unit, false, n->b);
    Expr *loop = mke(E_LOOP, ty_unit, n);
    loop->a = mk_op(OP_LT, ty_bool, n, 2, mk_local(vi, n), mk_local(vhi, n), NULL);
    loop->b = mk_let(x, mk_local(vi, n), body, n);
    Expr *inc = mke(E_ASSIGN, ty_unit, n);
    inc->var = vi;
    inc->a = mk_op(OP_ADD, ty_nat, n, 2, mk_local(vi, n), vstep ? mk_local(vstep, n) : step, NULL);
    loop->c = inc;
    result = mk_let(vi, lo, loop, n);
    if (vstep) result = mk_let(vstep, step, result, n);
    result = mk_let(vhi, hi, result, n);
  } else {
    Expr *coll = elab(it, NULL);
    Type *ct = ty_strip(coll->type);
    bool bytes = ct == ty_bytes;
    if (ct->kind != K_ARRAY && !bytes) error_at(it, "cannot iterate over %s (supported: ranges, Array, ByteArray)", ty_name(ct));
    Type *et = bytes ? ty_u8 : ct->elem;
    Var *vc = new_var(NULL, ct, false), *vi = new_var(NULL, ty_nat, true), *vn = new_var(NULL, ty_nat, false);
    Var *x = new_var(n->name, et, false);
    bind(x, n);
    Expr *body = elab_stmts(n->b->list, n->b->n, ty_unit, false, n->b);
    Expr *loop = mke(E_LOOP, ty_unit, n);
    loop->a = mk_op(OP_LT, ty_bool, n, 2, mk_local(vi, n), mk_local(vn, n), NULL);
    loop->b = mk_let(x, mk_op(bytes ? OP_BA_GET : OP_ARR_GET, et, n, 2, mk_local(vc, n), mk_local(vi, n), NULL), body, n);
    Expr *inc = mke(E_ASSIGN, ty_unit, n);
    inc->var = vi;
    inc->a = mk_op(OP_ADD, ty_nat, n, 2, mk_local(vi, n), mk_int(1, ty_nat, n), NULL);
    loop->c = inc;
    Expr *size = mk_op(bytes ? OP_BA_SIZE : OP_ARR_SIZE, ty_nat, n, 1, mk_local(vc, n), NULL, NULL);
    result = mk_let(vc, coll, mk_let(vn, size, mk_let(vi, mk_int(0, ty_nat, n), loop, n), n), n);
  }
  cx->loop_depth--;
  cx->nscope = mark;
  return result;
}

static Expr *elab_block_seq(Node *n, Type *expected, bool tail) {
  int mark = cx->nscope;
  Expr *e = n->kind == N_DO ? elab_stmts(n->list, n->n, expected, tail, n) : elab(n, expected);
  cx->nscope = mark;
  return e;
}

// One statement that is not a `let` (those scope over the rest of the block).
static Expr *elab_stmt(Node *n, Type *expected, bool tail) {
  switch (n->kind) {
  case N_ASSIGN: {
    Var *v = find_local(n->name);
    if (!v) error_at(n, "unknown variable '%s'", n->name);
    if (!v->is_mut) error_at(n, "'%s' is not mutable; declare it with `let mut`", n->name);
    Expr *rhs = elab(n->a, v->type);
    check_type(rhs, v->type, n->a);
    if (rhs->type->io && !(n->flag & 2)) error_at(n, "this is an IO action; use `%s ← ...`", n->name);
    Expr *e = mke(E_ASSIGN, ty_unit, n);
    e->var = v;
    e->a = rhs;
    return e;
  }
  case N_FOR: return elab_for(n);
  case N_WHILE:
  case N_REPEAT: {
    Expr *loop = mke(E_LOOP, ty_unit, n);
    if (n->a) {
      loop->a = elab(n->a, ty_bool);
      check_type(loop->a, ty_bool, n->a);
    }
    cx->loop_depth++;
    loop->b = elab_block_seq(n->b, ty_unit, false);
    cx->loop_depth--;
    return loop;
  }
  case N_UNLESS: {
    Expr *e = mke(E_IF, ty_unit, n);
    e->a = elab(n->a, ty_bool);
    check_type(e->a, ty_bool, n->a);
    e->b = mk_unit(n);
    e->c = elab_block_seq(n->b, ty_unit, false);
    return e;
  }
  case N_IF:
    if (n->flag == 1) {
      Expr *e = mke(E_IF, ty_unit, n);
      e->a = elab(n->a, ty_bool);
      check_type(e->a, ty_bool, n->a);
      Type *want = (tail && n->c) ? expected : ty_unit;
      e->b = elab_block_seq(n->b, want, tail && n->c);
      if (!want && ty_strip(e->b->type)->kind != K_NEVER) want = ty_strip(e->b->type);
      e->c = n->c ? elab_block_seq(n->c, want, tail) : mk_unit(n);
      if (!want && ty_strip(e->c->type)->kind != K_NEVER) want = ty_strip(e->c->type);
      bool bn = ty_strip(e->b->type)->kind == K_NEVER, cn = ty_strip(e->c->type)->kind == K_NEVER;
      if (!n->c) {
        // `if c then return x` falls through to the following statements
        e->type = ty_unit;
        if (!bn) check_type(e->b, ty_unit, n->b);
      } else {
        e->type = bn && cn ? ty_never : want ? want : ty_unit;
        if (!bn) check_type(e->b, e->type, n->b);
        if (!cn) check_type(e->c, e->type, n->c);
      }
      return e;
    }
    break;
  case N_MATCH:
    if (n->flag == 1) {
      StmtArg sa = {tail};
      return elab_match(n, tail ? expected : ty_unit, stmt_body, &sa);
    }
    break;
  case N_RETURN: {
    Expr *blk = cx->block;
    if (!blk) error_at(n, "'return' outside of a do block");
    Expr *e = mke(E_RETURN, ty_never, n);
    e->block = blk;
    e->a = n->a ? elab(n->a, blk->type) : mk_unit(n);
    if (!blk->type && ty_strip(e->a->type)->kind != K_NEVER) blk->type = ty_strip(e->a->type);
    check_type(e->a, blk->type, n);
    return e;
  }
  case N_BREAK:
  case N_CONTINUE: {
    if (cx->loop_depth == 0) error_at(n, "'%s' outside of a loop", n->kind == N_BREAK ? "break" : "continue");
    return mke(n->kind == N_BREAK ? E_BREAK : E_CONTINUE, ty_never, n);
  }
  case N_DO: return elab_block_seq(n, expected, tail);
  }
  return elab(n, tail ? expected : ty_unit);
}

static Expr *elab_stmts(Node **list, int n, Type *expected, bool tail, Node *at) {
  if (n == 0) return mk_unit(at);
  Node *s = list[0];
  bool last = n == 1;
  if (s->kind == N_LET && !s->c) {
    Expr *init = elab_let_init(s);
    if (s->a) return elab_let_pat(s, init, list + 1, n - 1, expected, tail, NULL);
    int mark = cx->nscope;
    Var *v = new_var(s->name, init->type, s->flag & 1);
    if (s->name != S("_")) bind(v, s);
    Expr *body = elab_stmts(list + 1, n - 1, expected, tail, s);
    cx->nscope = mark;
    return mk_let(v, init, body, s);
  }
  Expr *e = elab_stmt(s, expected, tail && last);
  if (last) {
    if (!tail && ty_strip(e->type)->kind != K_NEVER) check_type(e, ty_unit, s);
    return e;
  }
  Type *t = ty_strip(e->type);
  if (t->kind != K_UNIT && t->kind != K_NEVER)
    error_at(s, "this statement produces a %s that is discarded; bind it with `let _ ← ...`", ty_name(t));
  Expr *rest = elab_stmts(list + 1, n - 1, expected, tail, s);
  return seq2(e, rest, s);
}

static Expr *elab_do(Node *n, Type *expected) {
  Expr *blk = mke(E_BLOCK, expected ? ty_strip(expected) : NULL, n);
  Expr *save = cx->block;
  int save_depth = cx->loop_depth, mark = cx->nscope;
  cx->block = blk;
  cx->loop_depth = 0;
  blk->a = elab_stmts(n->list, n->n, blk->type, true, n);
  if (!blk->type) blk->type = ty_strip(blk->a->type);
  if (ty_strip(blk->a->type)->kind != K_NEVER && ty_strip(blk->type)->kind != K_UNIT) check_type(blk->a, blk->type, n);
  if (blk->type->kind == K_NEVER) blk->type = ty_unit;
  cx->block = save;
  cx->loop_depth = save_depth;
  cx->nscope = mark;
  return blk;
}

static Expr *elab(Node *n, Type *expected) {
  switch (n->kind) {
  case N_NUM: {
    Type *t = expected && (ty_is_int(expected) || ty_strip(expected) == ty_char) ? ty_strip(expected) : ty_nat;
    if (t == ty_char) t = ty_nat;
    return mk_int(n->num, t, n);
  }
  case N_CHAR: return mk_int(n->num, ty_char, n);
  case N_STR: {
    Expr *e = mke(E_STR, ty_string, n);
    e->num = (u64)intern_strlit(n->str, n->slen);
    return e;
  }
  case N_INTERP: {
    Expr *acc = NULL;
    for (int i = 0; i < n->n; i++) {
      Expr *part = to_string(elab(n->list[i], NULL), n->list[i]);
      acc = acc ? str_append(acc, part, n) : part;
    }
    if (!acc) {
      acc = mke(E_STR, ty_string, n);
      acc->num = (u64)intern_strlit("", 0);
    }
    return acc;
  }
  case N_UNIT: return mk_unit(n);
  case N_IDENT: case N_FIELD: case N_DOTID: return elab_app(n, NULL, 0, expected, n);
  case N_APP: return elab_app(n->a, n->list, n->n, expected, n);
  case N_INDEX: {
    Expr *a = elab(n->a, NULL);
    Type *t = ty_strip(a->type);
    Expr *i = elab(n->b, ty_nat);
    if (!ty_is_int(i->type)) error_at(n->b, "index must be a Nat or USize, got %s", ty_name(i->type));
    i = conv(i, ty_nat, n);
    if (t->kind == K_ARRAY) return mk_op(OP_ARR_GET, t->elem, n, 2, a, i, NULL);
    if (t == ty_bytes) return mk_op(OP_BA_GET, ty_u8, n, 2, a, i, NULL);
    error_at(n, "cannot index into %s", ty_name(t));
  }
  case N_BINOP: return elab_binop(n, expected);
  case N_UNOP: {
    if (n->name == S("!")) {
      Expr *a = elab(n->a, ty_bool);
      check_type(a, ty_bool, n->a);
      return mk_op(OP_LNOT, ty_bool, n, 1, a, NULL, NULL);
    }
    Expr *a = elab(n->a, expected && ty_is_int(expected) ? ty_strip(expected) : NULL);
    Type *t = ty_strip(a->type);
    if (!ty_is_int(t)) error_at(n, "operator '%s' needs an integer type", n->name);
    if (n->name == S("~~~")) {
      if (t == ty_nat) error_at(n, "'~~~' is not defined on Nat");
      return mk_op(OP_NOT, t, n, 1, a, NULL, NULL);
    }
    if (t == ty_nat) error_at(n, "unary minus is not defined on Nat");
    return mk_op(OP_SUB, t, n, 2, mk_int(0, t, n), a, NULL);
  }
  case N_IF: {
    if (n->flag == 1) return elab_stmt(n, expected, true);
    Expr *e = mke(E_IF, NULL, n);
    e->a = elab(n->a, ty_bool);
    check_type(e->a, ty_bool, n->a);
    if (!expected && is_literalish(n->b)) {
      e->c = elab(n->c, NULL);
      e->b = elab(n->b, e->c->type);
      e->type = e->c->type;
      return e;
    }
    e->b = elab(n->b, expected);
    bool bn = ty_strip(e->b->type)->kind == K_NEVER;
    e->c = elab(n->c, bn ? expected : e->b->type);
    if (!bn) check_type(e->c, e->b->type, n->c);
    e->type = bn ? e->c->type : e->b->type;
    return e;
  }
  case N_MATCH: {
    if (n->flag == 1) {
      StmtArg sa = {true};
      return elab_match(n, expected, stmt_body, &sa);
    }
    return elab_match(n, expected, term_body, NULL);
  }
  case N_LET: {
    Expr *init = elab_let_init(n);
    if (!n->c) error_at(n, "'let' without a body is only allowed inside a do block");
    if (n->a) return elab_let_pat(n, init, NULL, 0, expected, false, n->c);
    int mark = cx->nscope;
    Var *v = new_var(n->name, init->type, false);
    if (n->name != S("_")) bind(v, n);
    Expr *body = elab(n->c, expected);
    cx->nscope = mark;
    return mk_let(v, init, body, n);
  }
  case N_DO: return elab_do(n, expected);
  case N_STRUCT: return elab_struct(n, expected);
  case N_ANON: {
    Type *t = expected ? ty_strip(expected) : NULL;
    if (!t) error_at(n, "anonymous constructor ⟨...⟩ needs a known expected type");
    if (t->kind == K_PROD) return elab_tuple(n->list, n->n, t, n);
    if (t->kind != K_STRUCT) error_at(n, "anonymous constructor used where %s is expected", ty_name(t));
    resolve_decl(t->decl);
    return elab_ctor_app(t, 0, n->list, n->n, n);
  }
  case N_TUPLE: return elab_tuple(n->list, n->n, expected, n);
  case N_ARRLIT: {
    Type *t = expected ? ty_strip(expected) : NULL;
    Type *et = t && t->kind == K_ARRAY ? t->elem : NULL;
    Expr *e = mke(E_ARRLIT, NULL, n);
    e->nargs = n->n;
    e->args = xalloc(sizeof(Expr *) * (u64)(n->n + 1));
    for (int i = 0; i < n->n; i++) {
      e->args[i] = elab_arg(n->list[i], et);
      if (!et) et = ty_strip(e->args[i]->type);
    }
    if (!et) error_at(n, "cannot infer the element type of #[]; add a type annotation");
    e->type = ty_array(et);
    return e;
  }
  case N_ASCRIBE: {
    Type *t = resolve_type(n->type, cx->decl, true);
    Expr *e = elab(n->a, t);
    check_type(e, t, n);
    return e;
  }
  case N_NESTED: {
    Expr *e = elab(n->a, expected);
    if (!e->type->io) return e;
    // running the action here yields its plain result
    Var *v = new_var(NULL, e->type, false);
    return mk_let(v, e, mk_local(v, n), n);
  }
  case N_RANGE: error_at(n, "ranges can only be used in `for x in [a:b]`");
  case N_ASSIGN: case N_FOR: case N_WHILE: case N_REPEAT: case N_UNLESS: case N_RETURN: case N_BREAK:
  case N_CONTINUE:
    if (!cx->block) error_at(n, "statement outside of a do block");
    return elab_stmt(n, expected, false);
  }
  error_at(n, "unsupported expression");
}

// --------------------------------------------------------------- top level
void elab_func(Func *f) {
  if (f->compiled) return;
  f->compiled = true;
  resolve_sig(f);
  Ctx c = {0};
  Ctx *save = cx;
  cx = &c;
  c.decl = f->node;
  for (int i = 0; i < f->nparams; i++) {
    Var *v = new_var(f->pnames[i], f->ptypes[i], false);
    v->is_param = true;
    v->slot = i;
    bind(v, f->node);
  }
  Type *ret = ty_strip(f->ret);
  Expr *body = elab(f->node->a, ret);
  if (ret->kind != K_UNIT || ty_strip(body->type)->kind != K_NEVER) check_type(body, ret, f->node->a);
  f->body = body;
  f->vars = c.vars;
  f->nvars = c.nvars;
  cx = save;
}

void elab_global(Global *g) {
  if (g->compiled) {
    if (!g->type) error_at(g->node, "constant '%s' is defined in terms of itself", g->name);
    return;
  }
  g->compiled = true;
  Ctx c = {0};
  Ctx *save = cx;
  cx = &c;
  c.decl = g->node;
  if (!g->node->type) error_at(g->node, "'%s' needs an explicit type", g->name);
  Type *t = resolve_type(g->node->type, g->node, false);
  Expr *init = elab(g->node->a, t);
  check_type(init, t, g->node->a);
  g->init = init;
  g->type = t;
  g->vars = c.vars;
  g->nvars = c.nvars;
  cx = save;
  if (init->kind == E_INT) return; // inlined at every use: no storage, no initialiser
  g->index = nglobals++;
  if (ngwork == capgwork) {
    int cap = capgwork ? capgwork * 2 : 16;
    Global **n = xalloc(sizeof(Global *) * (u64)cap);
    memcpy(n, gwork, sizeof(Global *) * (u64)ngwork);
    gwork = n;
    capgwork = cap;
  }
  gwork[ngwork++] = g;
}

// ------------------------------------------------------------- optimisation
//
// Two small IR-level optimisations that matter a great deal for the kind of
// code this compiler exists for (hashes, field arithmetic): constant folding
// and inlining of `@[inline]` helpers such as `rotr`.

static Expr *fold(Expr *e) {
  if (e->kind != E_OP || e->nargs < 1 || e->nargs > 2) return e;
  for (int i = 0; i < e->nargs; i++)
    if (e->args[i]->kind != E_INT) return e;
  Type *t = ty_strip(e->type), *at = ty_strip(e->args[0]->type);
  u64 a = e->args[0]->num, b = e->nargs == 2 ? e->args[1]->num : 0, r;
  bool nat = at->kind == K_NAT;
  int bits = ty_bits(at);
  switch (e->num) {
  case OP_ADD:
    r = a + b;
    if (nat && r < a) return e;
    break;
  case OP_SUB: r = nat ? (a >= b ? a - b : 0) : a - b; break;
  case OP_MUL:
    if (nat && a && b > ~0ull / a) return e;
    r = a * b;
    break;
  case OP_AND: r = a & b; break;
  case OP_OR: r = a | b; break;
  case OP_XOR: r = a ^ b; break;
  case OP_SHR:
    if (nat) r = b >= 64 ? 0 : a >> b;
    else r = a >> (b % (u64)bits);
    break;
  case OP_SHL:
    if (nat) {
      if (b >= 64 || (b && (a >> (64 - b)))) return e;
      r = a << b;
    } else {
      r = a << (b % (u64)bits);
    }
    break;
  case OP_CONV: r = a; break;
  default: return e;
  }
  Expr *k = mke(E_INT, t, NULL);
  k->line = e->line;
  int rb = ty_bits(t);
  k->num = rb >= 64 ? r : r & ((1ull << rb) - 1);
  return k;
}

typedef struct {
  Var *from;
  Expr *to; // replacement expression (cloned at each use)
} Sub;

static bool inline_ok(Expr *e) {
  if (!e) return true;
  switch (e->kind) {
  case E_INT: case E_STR: case E_LOCAL: case E_GLOBAL: case E_CALL: case E_OP: case E_CTOR: case E_PROJ: case E_IF:
  case E_LET: case E_ARRLIT: case E_UNIT: break;
  default: return false;
  }
  if (!inline_ok(e->a) || !inline_ok(e->b) || !inline_ok(e->c)) return false;
  for (int i = 0; i < e->nargs; i++)
    if (!inline_ok(e->args[i])) return false;
  return true;
}

static Expr *clone(Expr *e, Sub *subs, int *nsubs) {
  if (!e) return NULL;
  if (e->kind == E_LOCAL) {
    for (int i = *nsubs - 1; i >= 0; i--)
      if (subs[i].from == e->var) {
        Expr *r = xalloc(sizeof(Expr));
        *r = *subs[i].to;
        return r;
      }
    fatal("internal: inliner met a free variable");
  }
  Expr *r = xalloc(sizeof(Expr));
  *r = *e;
  if (e->kind == E_LET) {
    r->a = clone(e->a, subs, nsubs);
    Var *nv = new_var(e->var->name, e->var->type, e->var->is_mut);
    nv->hidden = e->var->hidden;
    if (*nsubs == 64) fatal("inliner: too many bindings");
    subs[*nsubs].from = e->var;
    subs[(*nsubs)++].to = mk_local(nv, NULL);
    r->var = nv;
    r->b = clone(e->b, subs, nsubs);
    (*nsubs)--;
    return r;
  }
  r->a = clone(e->a, subs, nsubs);
  r->b = clone(e->b, subs, nsubs);
  r->c = clone(e->c, subs, nsubs);
  if (e->nargs) {
    r->args = xalloc(sizeof(Expr *) * (u64)(e->nargs + 1));
    for (int i = 0; i < e->nargs; i++) r->args[i] = clone(e->args[i], subs, nsubs);
  }
  return fold(r);
}

static Expr *inline_expr(Expr *e, int depth) {
  if (!e) return NULL;
  e->a = inline_expr(e->a, depth);
  e->b = inline_expr(e->b, depth);
  e->c = inline_expr(e->c, depth);
  for (int i = 0; i < e->nargs; i++) e->args[i] = inline_expr(e->args[i], depth);
  for (int i = 0; i < e->narms; i++) e->arms[i].body = inline_expr(e->arms[i].body, depth);
  if (e->kind != E_CALL || depth >= 6) return fold(e);
  Func *f = e->fn;
  if (!(f->node->flag & 4) || !f->body || !inline_ok(f->body)) return e;
  Sub subs[64];
  int nsubs = 0;
  Var *temps[32];
  Expr *inits[32];
  int ntemps = 0;
  if (f->nparams > 32) return e;
  for (int i = 0; i < f->nparams; i++) {
    Expr *a = e->args[i];
    subs[nsubs].from = f->vars[i];
    if (a->kind == E_INT || (a->kind == E_LOCAL && !ty_is_ptr(a->type))) {
      subs[nsubs++].to = a;
    } else {
      Var *t = new_var(NULL, f->ptypes[i], false);
      temps[ntemps] = t;
      inits[ntemps++] = a;
      subs[nsubs++].to = mk_local(t, NULL);
    }
  }
  Expr *body = inline_expr(clone(f->body, subs, &nsubs), depth + 1);
  for (int i = ntemps - 1; i >= 0; i--) {
    Expr *let = mke(E_LET, body->type, NULL);
    let->line = e->line;
    let->var = temps[i];
    let->a = inits[i];
    let->b = body;
    body = let;
  }
  return body;
}

static void inline_into(Expr **body, Var ***vars, int *nvars) {
  Ctx c = {0};
  Ctx *save = cx;
  cx = &c;
  c.vars = *vars;
  c.nvars = c.capvars = *nvars;
  *body = inline_expr(*body, 0);
  *vars = c.vars;
  *nvars = c.nvars;
  cx = save;
}

void elab_finish_decls(void) {
  for (int i = 0; i < nwork; i++) inline_into(&work[i]->body, &work[i]->vars, &work[i]->nvars);
  for (int i = 0; i < ngwork; i++) inline_into(&gwork[i]->init, &gwork[i]->vars, &gwork[i]->nvars);
}
