// Ownership analysis.
//
// leanc keeps Lean's value semantics with reference counting, and gets
// in-place mutation the same way Lean does: `arr.set! i v` mutates when the
// array's reference count is 1. For that to happen in practice the *last*
// use of a variable has to hand its reference over instead of copying it.
// This pass finds those last uses with a backward liveness analysis over the
// structured IR and marks them as moves.
//
// The evaluation-order contract (shared with gen.c) is what makes
// `a := a.set! i (f a[i]!)` update in place: within one call/operator,
// operands that are plain variables are read *after* all compound operands
// have been evaluated, exactly as if the program were in A-normal form.
#include "leanc.h"

static int nwords;
typedef u64 *Set;

static Set set_new(void) { return xalloc(8 * (u64)nwords); }
static Set set_copy(Set s) {
  Set r = set_new();
  memcpy(r, s, 8 * (unsigned long)nwords);
  return r;
}
static void set_assign(Set d, Set s) { memcpy(d, s, 8 * (unsigned long)nwords); }
static void set_union(Set d, Set s) {
  for (int i = 0; i < nwords; i++) d[i] |= s[i];
}
static bool set_subset(Set a, Set b) {
  for (int i = 0; i < nwords; i++)
    if (a[i] & ~b[i]) return false;
  return true;
}
static bool has(Set s, Var *v) { return (s[v->id >> 6] >> (v->id & 63)) & 1; }
static void add(Set s, Var *v) { s[v->id >> 6] |= 1ull << (v->id & 63); }
static void del(Set s, Var *v) { s[v->id >> 6] &= ~(1ull << (v->id & 63)); }

typedef struct LoopCtx {
  Set brk, cont;
  struct LoopCtx *up;
} LoopCtx;
typedef struct BlockCtx {
  Expr *block;
  Set after;
  struct BlockCtx *up;
} BlockCtx;
static LoopCtx *loops;
static BlockCtx *blocks;

// A "path" is a chain of field projections rooted at a variable or global
// constant. Paths can be borrowed: the root keeps everything alive.
bool expr_is_path(Expr *e) {
  if (e->kind == E_LOCAL || e->kind == E_GLOBAL) return true;
  if (e->kind == E_PROJ) return expr_is_path(e->a);
  return false;
}

static Var *path_root(Expr *e) {
  while (e->kind == E_PROJ) e = e->a;
  return e->kind == E_LOCAL ? e->var : NULL;
}

// Ownership mode of every operand of an operator: 'o' consumed, 'b' borrowed.
void op_modes(Expr *e, char *m) {
  int n = e->nargs;
  for (int i = 0; i < n; i++) m[i] = 'o';
  m[n] = 0;
  if (e->kind != E_OP) return;
  switch (e->num) {
  case OP_ARR_GET: case OP_ARR_SIZE: case OP_BA_GET: case OP_BA_SIZE: case OP_TAG: case OP_OPT_GET: case OP_PANIC:
    m[0] = 'b';
    break;
  case OP_ARR_REPLICATE: m[1] = 'b'; break;
  case OP_RTCALL:
    for (int i = 0; i < n; i++) m[i] = e->own[i];
    break;
  case OP_INTRIN:
    if (e->num2 == IN_PTR) m[0] = 'b';
    break;
  }
}

// An operand whose read is deferred until the operator itself executes.
bool operand_deferred(Expr *a, char mode) {
  if (a->kind == E_LOCAL || a->kind == E_INT || a->kind == E_STR) return true;
  return mode == 'b' && expr_is_path(a) && ty_is_ptr(a->type);
}

static void walk(Expr *e, Set live);

static void walk_operands(Expr **args, int n, const char *modes, Set live) {
  // reverse of: [compound operands in order] then [deferred operands in order]
  for (int i = n - 1; i >= 0; i--) {
    Expr *a = args[i];
    if (!operand_deferred(a, modes[i]) || modes[i] != 'b') continue;
    Var *r = path_root(a);
    if (r) add(live, r);
    if (a->kind == E_LOCAL) a->move = false;
  }
  for (int i = n - 1; i >= 0; i--) {
    Expr *a = args[i];
    if (!operand_deferred(a, modes[i]) || modes[i] == 'b') continue;
    if (a->kind == E_LOCAL) {
      a->move = ty_is_ptr(a->type) && !has(live, a->var);
      add(live, a->var);
    }
  }
  for (int i = n - 1; i >= 0; i--)
    if (!operand_deferred(args[i], modes[i])) walk(args[i], live);
}

static void pat_unbind(Pat *p, Set live) {
  if (p->kind == P_VAR) del(live, p->var);
  for (int i = 0; i < p->nsub; i++) pat_unbind(p->sub[i], live);
}

static void walk(Expr *e, Set live) {
  char modes_buf[64];
  char *modes = e->nargs >= 62 ? xalloc((u64)e->nargs + 2) : modes_buf;
  switch (e->kind) {
  case E_INT: case E_STR: case E_UNIT: case E_GLOBAL: return;
  case E_LOCAL:
    e->move = ty_is_ptr(e->type) && !has(live, e->var);
    add(live, e->var);
    return;
  case E_CALL: case E_CTOR: case E_ARRLIT: case E_OP:
    op_modes(e, modes);
    walk_operands(e->args, e->nargs, modes, live);
    return;
  case E_PROJ:
    if (expr_is_path(e->a)) {
      Var *r = path_root(e->a);
      if (r) add(live, r);
      Expr *leaf = e->a;
      while (leaf->kind == E_PROJ) leaf = leaf->a;
      leaf->move = false;
    } else {
      walk(e->a, live);
    }
    return;
  case E_UPDATE: {
    // operands: values..., then the base object last
    int n = e->nargs + 1;
    if (n >= 63) fatal("too many fields in structure update");
    Expr *ops[64];
    for (int i = 0; i < e->nargs; i++) ops[i] = e->args[i], modes[i] = 'o';
    ops[e->nargs] = e->a;
    modes[e->nargs] = 'o';
    walk_operands(ops, n, modes, live);
    return;
  }
  case E_IF: {
    Set lb = set_copy(live), lc = set_copy(live);
    walk(e->b, lb);
    walk(e->c, lc);
    set_assign(live, lb);
    set_union(live, lc);
    walk(e->a, live);
    return;
  }
  case E_LET:
    walk(e->b, live);
    del(live, e->var);
    walk(e->a, live);
    return;
  case E_SEQ:
    for (int i = e->nargs - 1; i >= 0; i--) walk(e->args[i], live);
    return;
  case E_ASSIGN:
    del(live, e->var);
    walk(e->a, live);
    return;
  case E_LOOP: {
    Set after = set_copy(live);
    Set head = set_copy(after);
    for (;;) {
      Set lp = set_copy(head);
      if (e->c) walk(e->c, lp);
      LoopCtx lc = {after, lp, loops};
      loops = &lc;
      Set lb = set_copy(lp);
      walk(e->b, lb);
      loops = lc.up;
      if (e->a) {
        set_union(lb, after);
        walk(e->a, lb);
      }
      if (set_subset(lb, head)) break;
      set_union(head, lb);
    }
    set_assign(live, head);
    return;
  }
  case E_BREAK: set_assign(live, loops->brk); return;
  case E_CONTINUE: set_assign(live, loops->cont); return;
  case E_RETURN: {
    BlockCtx *b = blocks;
    while (b && b->block != e->block) b = b->up;
    if (!b) fatal("internal: return target not found");
    set_assign(live, b->after);
    walk(e->a, live);
    return;
  }
  case E_BLOCK: {
    BlockCtx b = {e, set_copy(live), blocks};
    // a block suspends the enclosing loops: break/continue cannot cross it
    LoopCtx *save = loops;
    loops = NULL;
    blocks = &b;
    walk(e->a, live);
    blocks = b.up;
    loops = save;
    return;
  }
  case E_MATCH: {
    Set acc = set_new();
    for (int a = 0; a < e->narms; a++) {
      Set la = set_copy(live);
      walk(e->arms[a].body, la);
      for (int i = 0; i < e->arms[a].npats; i++) pat_unbind(e->arms[a].pats[i], la);
      set_union(acc, la);
    }
    set_assign(live, acc);
    for (int i = 0; i < e->nargs; i++) {
      e->args[i]->move = false;
      add(live, e->args[i]->var);
    }
    return;
  }
  }
  fatal("internal: liveness: unknown node %d", e->kind);
}

static void mark_moved(Expr *e) {
  if (!e) return;
  if (e->kind == E_LOCAL && e->move) e->var->moved = true;
  mark_moved(e->a);
  mark_moved(e->b);
  mark_moved(e->c);
  for (int i = 0; i < e->nargs; i++) mark_moved(e->args[i]);
  for (int i = 0; i < e->narms; i++) mark_moved(e->arms[i].body);
}

void live_func(Expr *body, Var **vars, int nvars) {
  (void)vars;
  nwords = (nvars + 63) / 64 + 1;
  loops = NULL;
  blocks = NULL;
  Set live = set_new();
  walk(body, live);
  mark_moved(body);
}
