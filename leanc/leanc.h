// leanc — a zero-dependency Lean 4 (subset) -> x86-64 ELF compiler.
//
// No libc, no LLVM, no assembler, no linker. The only thing needed to build
// this compiler is a C compiler; the only thing it needs at run time is a
// Linux kernel.
#ifndef LEANC_H
#define LEANC_H

typedef unsigned char u8;
typedef unsigned short u16;
typedef unsigned int u32;
typedef unsigned long long u64;
typedef long long i64;
// Macros rather than a typedef: C23 made bool, true and false keywords, and
// this file has to compile the same way under every C standard.
#define bool int
#define true 1
#define false 0
#define NULL ((void *)0)

// ---------------------------------------------------------------- platform
void *xalloc(u64 size); // zeroed, never freed
void plat_write(int fd, const void *buf, u64 len);
void plat_exit(int code) __attribute__((noreturn));
// Reads a whole file. Returns NULL if it cannot be opened.
char *plat_read_file(const char *path, u64 *len);
bool plat_write_file(const char *path, const void *buf, u64 len, int mode);

void *memcpy(void *d, const void *s, unsigned long n);
void *memset(void *d, int c, unsigned long n);
int memcmp(const void *a, const void *b, unsigned long n);
unsigned long strlen(const char *s);

// ------------------------------------------------------------------- utils
typedef struct {
  char *p;
  u64 len, cap;
} Buf;
void buf_put(Buf *b, const void *data, u64 len);
void buf_u8(Buf *b, u8 v);
void buf_u32(Buf *b, u32 v);
void buf_u64(Buf *b, u64 v);
void buf_str(Buf *b, const char *s);
void buf_fmt(Buf *b, const char *fmt, ...);
void buf_vfmt(Buf *b, const char *fmt, __builtin_va_list ap);

const char *intern(const char *s);
const char *intern_n(const char *s, int n);
const char *fmt(const char *fmt, ...); // interned result
bool str_starts(const char *s, const char *prefix);
const char *str_rchr(const char *s, char c);

void fatal_at(const char *file, int line, int col, const char *fmt, ...)
    __attribute__((noreturn));
void fatal(const char *fmt, ...) __attribute__((noreturn));

// ------------------------------------------------------------------- lexer
enum {
  T_EOF,
  T_IDENT,  // foo, Foo.bar, get!
  T_KW,     // reserved word (text interned)
  T_NUM,
  T_STR,
  T_CHAR,
  T_INTERP, // s!"..." raw body in str/slen
  T_SYM,    // punctuation (text interned)
  T_DOTID,  // .foo / .foo.bar   (space_before tells postfix vs leading)
  T_DOTNUM, // .1
};

typedef struct {
  int kind;
  const char *text; // interned: identifier / keyword / symbol
  u64 num;
  const char *str; // string literal bytes (unescaped) or raw interp body
  int slen;
  int line, col;
  bool space_before;
} Token;

typedef struct {
  const char *file;
  Token *toks;
  int ntoks;
} TokenStream;

TokenStream lex(const char *file, const char *src, u64 len, int line0, int col0);

// --------------------------------------------------------------------- AST
enum {
  N_NUM = 1,
  N_STR,
  N_CHAR,
  N_INTERP,   // list = parts (N_STR or expr)
  N_IDENT,    // name
  N_DOTID,    // name (leading-dot constructor / function)
  N_APP,      // a = fn, list = args
  N_FIELD,    // a = expr, name = field/method
  N_INDEX,    // a[b]  flag: '!' or '?' or 0
  N_BINOP,    // name = op, a, b
  N_UNOP,     // name = op, a
  N_IF,       // a = cond, b = then, c = else (may be NULL in do)
  N_MATCH,    // list = scrutinees, list2 = arms
  N_ARM,      // list = patterns, a = body
  N_LET,      // name / a = pattern, type, b = value, c = body (NULL in do); flag bit0 mut bit1 arrow
  N_DO,       // list = statements
  N_STRUCT,   // a = base (with) or NULL, list = N_FIELDINIT
  N_FIELDINIT,// name, a = value
  N_ANON,     // ⟨ list ⟩
  N_TUPLE,    // ( list )
  N_UNIT,     // ()
  N_ARRLIT,   // #[ list ]
  N_ASCRIBE,  // (a : type)
  N_NESTED,   // (← a)
  N_RANGE,    // [a:b:c]  a/c may be NULL
  N_ASSIGN,   // name := a   flag bit1 arrow
  N_FOR,      // name in a do b
  N_WHILE,    // a = cond, b = body
  N_REPEAT,   // b = body
  N_RETURN,   // a (may be NULL)
  N_BREAK,
  N_CONTINUE,
  N_UNLESS,   // a = cond, b = body
  N_FUN,
  // types
  N_TYNAME,   // name, list = args
  N_TYPROD,   // a × b
  N_TYFUN,    // a → b
  // declarations
  N_DEF,      // name, list = params (N_PARAM), type = return type, a = body, str = extern symbol
  N_PARAM,    // name, type
  N_STRUCTDECL, // name, list = fields (N_PARAM, a = default)
  N_INDDECL,  // name, list = ctors (N_CTORDECL: name, list = params)
  N_CTORDECL,
  N_ALIAS,    // abbrev name := type
};

typedef struct Node Node;
struct Node {
  int kind;
  int line, col;
  const char *file;
  const char *name;
  u64 num;
  const char *str;
  int slen;
  Node *a, *b, *c;
  Node **list;
  int n;
  Node **list2;
  int n2;
  Node *type;
  int flag;
  // declaration context (for name resolution inside bodies)
  const char *ns;        // enclosing namespace ("" if none)
  const char **opens;    // opened namespaces
  int nopens;
};

typedef struct {
  Node **decls;
  int ndecls;
  const char **imports;
  int nimports;
} Module;

Module parse_module(const char *file, const char *src, u64 len);

// ------------------------------------------------------------------- types
enum {
  K_NAT = 1,
  K_U8,
  K_U16,
  K_U32,
  K_U64,
  K_USIZE,
  K_BOOL,
  K_CHAR,
  K_UNIT,
  K_ENUM,   // inductive with only nullary constructors (scalar)
  // heap types below (is_ptr)
  K_STRING,
  K_BYTES,
  K_ARRAY,  // elem
  K_OPTION, // elem
  K_PROD,   // a, b
  K_STRUCT, // decl
  K_IND,    // decl (boxed inductive)
  K_NEVER,
  K_IO,     // IO-wrapped view: base type in elem
};

typedef struct Type Type;
typedef struct TypeDecl TypeDecl;
typedef struct Func Func;

typedef struct {
  const char *name;
  Type *type;
  Node *type_node;
  Node *dflt;
} Field;

typedef struct {
  const char *name; // short name
  Field *fields;
  int nfields;
} Ctor;

struct TypeDecl {
  const char *name; // fully qualified
  Node *node;
  Ctor *ctors;
  int nctors;
  bool is_struct;
  bool resolved, resolving;
  Type *type;
};

struct Type {
  int kind;
  Type *elem, *a, *b;
  TypeDecl *decl;
  bool io;        // IO-wrapped view of base type (base in elem)
  Type *io_type;  // cached IO wrapper
  const char *name;
  int drop_label; // codegen: label of drop function, 0 if not yet requested
  Type *next;
};

extern Type *ty_nat, *ty_u8, *ty_u16, *ty_u32, *ty_u64, *ty_usize, *ty_bool,
    *ty_char, *ty_unit, *ty_string, *ty_bytes, *ty_never;
Type *ty_array(Type *elem);
Type *ty_option(Type *elem);
Type *ty_prod(Type *a, Type *b);
Type *ty_io(Type *t);
Type *ty_strip(Type *t); // remove IO wrapper
bool ty_is_ptr(Type *t);
bool ty_is_int(Type *t);
int ty_bits(Type *t);
const char *ty_name(Type *t);
int ty_nctors(Type *t);
int ty_ctor_nfields(Type *t, int tag);
Type *ty_ctor_field(Type *t, int tag, int i);

// ---------------------------------------------------------------- typed IR
enum {
  E_INT = 1,  // num
  E_STR,      // num = string literal id
  E_LOCAL,    // var
  E_GLOBAL,   // glob
  E_CALL,     // fn, args
  E_OP,       // num = op, args
  E_CTOR,     // num = tag, args
  E_PROJ,     // a, num = field index (single-ctor types; num2 = tag)
  E_UPDATE,   // a = base, args = values, fields = indices
  E_IF,       // a, b, c
  E_LET,      // var, a = init, b = body
  E_SEQ,      // args
  E_ASSIGN,   // var, a
  E_LOOP,     // a = cond (or NULL), b = body, c = post (or NULL)
  E_RETURN,   // a ; block = target block or NULL for function
  E_BREAK,
  E_CONTINUE,
  E_BLOCK,    // a = body (term-level do block)
  E_MATCH,    // args = scrutinee vars (E_LOCAL of hidden vars), arms
  E_ARRLIT,   // args
  E_UNIT,
};

enum {
  OP_ADD = 1, OP_SUB, OP_MUL, OP_DIV, OP_MOD,
  OP_AND, OP_OR, OP_XOR, OP_SHL, OP_SHR, OP_NOT,
  OP_EQ, OP_NE, OP_LT, OP_LE, OP_GT, OP_GE,
  OP_LNOT,
  OP_CONV,       // numeric conversion to e->type
  OP_ARR_GET, OP_ARR_SET, OP_ARR_SIZE, OP_ARR_PUSH, OP_ARR_REPLICATE,
  OP_ARR_EMPTY,  // arg: capacity
  OP_ARR_POP,
  OP_BA_GET, OP_BA_SET, OP_BA_SIZE, OP_BA_PUSH,
  OP_TAG,        // constructor tag of boxed value
  OP_OPT_GET,    // Option.get!
  OP_RTCALL,     // call runtime function e->fn; ownership in e->own ("o"/"b" per arg)
  OP_CAST,       // reinterpret (String <-> ByteArray), owned -> owned
  OP_INTRIN,     // raw machine intrinsic, num2 = which
  OP_PANIC,      // args[0] = message string
};

enum {
  IN_SYSCALL = 1, IN_LOAD8, IN_LOAD16, IN_LOAD32, IN_LOAD64,
  IN_STORE8, IN_STORE16, IN_STORE32, IN_STORE64,
  IN_COPY, IN_FILL, IN_MEMEQ,
  IN_CAS32, IN_CAS64, IN_XADD64, IN_XCHG32, IN_PAUSE, IN_RDTSC,
  IN_PTR,     // address of heap object (borrowed arg)
  IN_OFPTR,   // reinterpret raw address as heap object (takes ownership)
  IN_DROPPED, // forget a value without releasing it
};

typedef struct Var Var;
struct Var {
  const char *name;
  Type *type;
  int id;      // index within function (liveness bit)
  int slot;    // frame slot (locals) or param index
  bool is_param;
  bool is_mut;
  bool moved;  // some reference moves out of this variable
  bool hidden;
};

typedef struct Global Global;
struct Global {
  const char *name;
  Type *type;
  Node *node;
  int index;       // slot in bss
  bool compiled;
  struct Expr *init;
  Var **vars;
  int nvars;
  Global *next;
};

typedef struct Pat Pat;
struct Pat {
  int kind; // P_WILD, P_VAR, P_INT, P_CTOR
  Var *var;
  u64 num;
  Type *type;
  Pat **sub;
  int nsub;
};
enum { P_WILD = 1, P_VAR, P_INT, P_CTOR };

typedef struct Expr Expr;
typedef struct {
  Pat **pats;
  int npats;
  Expr *body;
} Arm;

struct Expr {
  int kind;
  Type *type;
  int line;
  u64 num, num2;
  Var *var;
  Func *fn;
  Global *glob;
  Expr *a, *b, *c;
  Expr **args;
  int nargs;
  int *fields;
  Arm *arms;
  int narms;
  const char *own;
  bool move;        // E_LOCAL: this read moves the value out
  Expr *block;      // E_RETURN target
  int label;        // codegen scratch
  int depth;        // codegen scratch (scope depth)
};

struct Func {
  const char *name;
  Node *node;
  Type **ptypes;
  const char **pnames;
  int nparams;
  Type *ret;      // may be IO-wrapped
  const char *ext; // extern symbol, or NULL
  int intrin;     // IN_* if extern maps to an intrinsic
  bool sig_done;
  bool queued, compiled;
  Expr *body;
  Var **vars;
  int nvars;
  int label;      // code label
  Func *next;
};

// ---------------------------------------------------------------- elaborator
typedef struct {
  const char *bytes;
  int len;
  u64 addr; // data address of object, assigned at layout
} StrLit;

extern StrLit *strlits;
extern int nstrlits;
extern Global *globals_head;
extern int nglobals;

void types_init(void);
void elab_init(void);
void elab_add_module(Module *m);
void elab_finish_decls(void);
Func *elab_find_func(const char *name);
void elab_func(Func *f);        // elaborate body (on demand)
void elab_global(Global *g);
Func *elab_require(const char *name); // find + queue for compilation
extern Func **work;              // functions queued for codegen
extern int nwork;
extern Global **gwork;           // globals in initialisation order
extern int ngwork;
int intern_strlit(const char *bytes, int len);

// ------------------------------------------------------------------ liveness
void live_func(Expr *body, Var **vars, int nvars);
bool expr_is_path(Expr *e);
void op_modes(Expr *e, char *modes);
bool operand_deferred(Expr *a, char mode);

// ------------------------------------------------------------------- codegen
void gen_program(Func *main_fn, Buf *out);

#define TEXT_BASE 0x400000ull
#define DATA_BASE 0x10000000ull
#define BSS_BASE 0x20000000ull
#define BSS_RT_SIZE 0x1000ull // runtime scratch + allocator state (see rt/Rt.lean)

extern bool opt_verbose;

#endif
