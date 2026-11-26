// Parser for the Lean 4 subset: tokens -> AST.
//
// Lean's grammar is whitespace-sensitive in exactly one way that matters
// here: the "position" rule. A token can only continue the current
// application as an argument if its column is strictly greater than the
// column saved by the enclosing `let` / do-statement / command. That is
// what lets
//
//     let y := f x
//     g y
//
// parse as two things instead of `f x g y`. We track that column in
// `pos_col`; brackets reset it, exactly like Lean's `withoutPosition`.
#include "leanc.h"

typedef struct {
  const char *file;
  Token *toks;
  int pos;
  int pos_col;  // arguments must start at col > pos_col
  bool no_do;   // `do` may not start a trailing argument (for/while headers)
  const char *ns;
  const char **opens;
  int nopens;
} P;

static const char *S(const char *s) { return intern(s); }

static Token *peek(P *p) { return &p->toks[p->pos]; }
static Token *peek2(P *p) { return peek(p)->kind == T_EOF ? peek(p) : &p->toks[p->pos + 1]; }
static Token *next(P *p) {
  Token *t = &p->toks[p->pos];
  if (t->kind != T_EOF) p->pos++;
  return t;
}
static bool tok_is(Token *t, int kind, const char *text) { return t->kind == kind && t->text == S(text); }
static bool is_sym(P *p, const char *s) { return tok_is(peek(p), T_SYM, s); }
static bool is_kw(P *p, const char *s) { return tok_is(peek(p), T_KW, s); }

static const char *tok_desc(Token *t) {
  switch (t->kind) {
  case T_EOF: return "end of file";
  case T_NUM: return "number";
  case T_STR: case T_INTERP: return "string";
  case T_CHAR: return "character";
  case T_DOTID: return fmt(".%s", t->text);
  case T_DOTNUM: return "tuple projection";
  default: return fmt("'%s'", t->text);
  }
}

static void err(P *p, Token *t, const char *msg) {
  fatal_at(p->file, t->line, t->col, "%s (at %s)", msg, tok_desc(t));
}

static bool accept_sym(P *p, const char *s) {
  if (is_sym(p, s)) {
    next(p);
    return true;
  }
  return false;
}
static bool accept_kw(P *p, const char *s) {
  if (is_kw(p, s)) {
    next(p);
    return true;
  }
  return false;
}
static Token *expect_sym(P *p, const char *s) {
  if (!is_sym(p, s)) err(p, peek(p), fmt("expected '%s'", s));
  return next(p);
}
static Token *expect_kw(P *p, const char *s) {
  if (!is_kw(p, s)) err(p, peek(p), fmt("expected '%s'", s));
  return next(p);
}
static const char *expect_ident(P *p) {
  if (peek(p)->kind != T_IDENT) err(p, peek(p), "expected identifier");
  return next(p)->text;
}

static Node *mk(P *p, int kind, Token *at) {
  Node *n = xalloc(sizeof(Node));
  n->kind = kind;
  n->line = at->line;
  n->col = at->col;
  n->file = p->file;
  return n;
}

typedef struct {
  Node **v;
  int n, cap;
} Vec;
static void vpush(Vec *v, Node *x) {
  if (v->n == v->cap) {
    int cap = v->cap ? v->cap * 2 : 4;
    Node **nv = xalloc(sizeof(Node *) * (u64)cap);
    memcpy(nv, v->v, sizeof(Node *) * (u64)v->n);
    v->v = nv;
    v->cap = cap;
  }
  v->v[v->n++] = x;
}

static Node *parse_expr(P *p, int minprec);
static Node *parse_block(P *p, Token *intro);
static Node *parse_stmt(P *p);
static Node *parse_type(P *p);

// ------------------------------------------------------------------- types
static bool is_generic_type(const char *name) {
  return name == S("Array") || name == S("Option") || name == S("IO") || name == S("List");
}

static Node *parse_type_atom(P *p) {
  Token *t = peek(p);
  if (accept_sym(p, "(")) {
    int save = p->pos_col;
    p->pos_col = -1;
    Node *n = parse_type(p);
    expect_sym(p, ")");
    p->pos_col = save;
    return n;
  }
  if (t->kind != T_IDENT) err(p, t, "expected a type");
  next(p);
  Node *n = mk(p, N_TYNAME, t);
  n->name = t->text;
  return n;
}

static Node *parse_type(P *p) {
  Node *n = parse_type_atom(p);
  if (n->kind == N_TYNAME && n->n == 0 && is_generic_type(n->name)) {
    Vec args = {0};
    vpush(&args, parse_type_atom(p));
    // nested generic without parentheses is not valid Lean either
    n->list = args.v;
    n->n = args.n;
  }
  Token *t = peek(p);
  if (accept_sym(p, "×")) {
    Node *pr = mk(p, N_TYPROD, t);
    pr->a = n;
    pr->b = parse_type(p);
    return pr;
  }
  if (is_sym(p, "→") || is_sym(p, "->")) {
    next(p);
    Node *fn = mk(p, N_TYFUN, t);
    fn->a = n;
    fn->b = parse_type(p);
    return fn;
  }
  return n;
}

// ------------------------------------------------------------- expressions
typedef struct {
  const char *sym;
  int prec;
  bool right;
} BinOp;
static const BinOp binops[] = {
    {"||", 30, false}, {"∨", 30, false},  {"&&", 35, false},  {"∧", 35, false},
    {"==", 50, false}, {"!=", 50, false}, {"≠", 50, false},   {"<", 50, false},
    {">", 50, false},  {"<=", 50, false}, {"≤", 50, false},   {">=", 50, false},
    {"≥", 50, false},  {"=", 50, false},  {"|||", 55, false}, {"^^^", 58, false},
    {"&&&", 60, false}, {"++", 65, false}, {"+", 65, false},  {"-", 65, false},
    {"*", 70, false},  {"/", 70, false},  {"%", 70, false},   {"<<<", 75, false},
    {">>>", 75, false}, {NULL, 0, false}};

static bool can_start_arg(P *p, Token *t) {
  switch (t->kind) {
  case T_IDENT: case T_NUM: case T_STR: case T_CHAR: case T_INTERP: return true;
  case T_DOTID: return t->space_before;
  case T_KW: return t->text == S("do") && !p->no_do;
  case T_SYM:
    if (t->text == S("(") || t->text == S("⟨") || t->text == S("#[") || t->text == S("{")) return true;
    if (t->text == S("[")) return t->space_before;
    return false;
  }
  return false;
}

static Node *parse_interp(P *p, Token *t) {
  // split  text{expr}text  into parts
  Node *n = mk(p, N_INTERP, t);
  Vec parts = {0};
  const char *s = t->str;
  int len = t->slen, i = 0;
  Buf lit = {0};
  while (i <= len) {
    if (i == len || s[i] == '{') {
      if (lit.len) {
        // re-lex the literal chunk to process escapes
        Buf q = {0};
        buf_u8(&q, '"');
        buf_put(&q, lit.p, lit.len);
        buf_u8(&q, '"');
        TokenStream ts = lex(p->file, q.p, q.len, t->line, t->col);
        Node *sn = mk(p, N_STR, t);
        sn->str = ts.toks[0].str;
        sn->slen = ts.toks[0].slen;
        vpush(&parts, sn);
        lit.len = 0;
      }
      if (i == len) break;
      int depth = 1, j = i + 1;
      while (j < len && depth > 0) {
        if (s[j] == '{') depth++;
        if (s[j] == '}') depth--;
        j++;
      }
      if (depth) fatal_at(p->file, t->line, t->col, "unbalanced '{' in interpolated string");
      TokenStream ts = lex(p->file, s + i + 1, (u64)(j - i - 2), t->line, t->col);
      P sub = *p;
      sub.toks = ts.toks;
      sub.pos = 0;
      sub.pos_col = -1;
      sub.no_do = false;
      vpush(&parts, parse_expr(&sub, 0));
      if (peek(&sub)->kind != T_EOF) err(&sub, peek(&sub), "unexpected token in interpolation");
      i = j;
    } else {
      if (s[i] == '\\' && i + 1 < len) buf_u8(&lit, (u8)s[i++]);
      buf_u8(&lit, (u8)s[i++]);
    }
  }
  n->list = parts.v;
  n->n = parts.n;
  return n;
}

static Node *parse_match(P *p, bool in_do) {
  Token *t = expect_kw(p, "match");
  Node *n = mk(p, N_MATCH, t);
  Vec scr = {0};
  do {
    vpush(&scr, parse_expr(p, 0));
  } while (accept_sym(p, ","));
  expect_kw(p, "with");
  n->list = scr.v;
  n->n = scr.n;
  Vec arms = {0};
  while (is_sym(p, "|")) {
    Vec alts = {0}; // each alt is an N_ARM with only patterns filled in
    Token *arrow = NULL;
    while (accept_sym(p, "|")) {
      Node *arm = mk(p, N_ARM, peek(p));
      Vec pats = {0};
      do {
        vpush(&pats, parse_expr(p, 80));
      } while (accept_sym(p, ","));
      arm->list = pats.v;
      arm->n = pats.n;
      vpush(&alts, arm);
      if (is_sym(p, "=>")) break;
    }
    arrow = expect_sym(p, "=>");
    Node *body = in_do ? parse_block(p, arrow) : parse_expr(p, 0);
    for (int i = 0; i < alts.n; i++) {
      alts.v[i]->a = body;
      vpush(&arms, alts.v[i]);
    }
  }
  if (arms.n == 0) err(p, peek(p), "expected match alternatives");
  n->list2 = arms.v;
  n->n2 = arms.n;
  return n;
}

// let [mut] (name | pattern) [: T] (:= | ←) value      (body handled by caller)
static Node *parse_let_head(P *p) {
  Token *t = expect_kw(p, "let");
  Node *n = mk(p, N_LET, t);
  int save = p->pos_col;
  p->pos_col = t->col;
  if (accept_kw(p, "mut")) n->flag |= 1;
  if (is_sym(p, "(") || is_sym(p, "⟨")) {
    n->a = parse_expr(p, 80);
  } else {
    n->name = expect_ident(p);
  }
  if (accept_sym(p, ":")) n->type = parse_type(p);
  if (is_sym(p, "←") || is_sym(p, "<-")) {
    next(p);
    n->flag |= 2;
  } else {
    expect_sym(p, ":=");
  }
  n->b = parse_expr(p, 0);
  p->pos_col = save;
  return n;
}

static Node *parse_primary(P *p) {
  Token *t = peek(p);
  switch (t->kind) {
  case T_NUM: {
    next(p);
    Node *n = mk(p, N_NUM, t);
    n->num = t->num;
    return n;
  }
  case T_CHAR: {
    next(p);
    Node *n = mk(p, N_CHAR, t);
    n->num = t->num;
    return n;
  }
  case T_STR: {
    next(p);
    Node *n = mk(p, N_STR, t);
    n->str = t->str;
    n->slen = t->slen;
    return n;
  }
  case T_INTERP: next(p); return parse_interp(p, t);
  case T_IDENT: {
    next(p);
    Node *n = mk(p, N_IDENT, t);
    n->name = t->text;
    return n;
  }
  case T_DOTID: {
    next(p);
    Node *n = mk(p, N_DOTID, t);
    n->name = t->text;
    return n;
  }
  case T_KW:
    if (t->text == S("if")) {
      next(p);
      Node *n = mk(p, N_IF, t);
      n->a = parse_expr(p, 0);
      expect_kw(p, "then");
      n->b = parse_expr(p, 0);
      expect_kw(p, "else");
      n->c = parse_expr(p, 0);
      return n;
    }
    if (t->text == S("match")) return parse_match(p, false);
    if (t->text == S("let")) {
      Node *n = parse_let_head(p);
      accept_sym(p, ";");
      n->c = parse_expr(p, 0);
      return n;
    }
    if (t->text == S("do")) {
      next(p);
      return parse_block(p, t);
    }
    if (t->text == S("fun")) err(p, t, "lambdas are not supported by leanc yet");
    break;
  case T_SYM: {
    int save_col = p->pos_col;
    bool save_do = p->no_do;
    if (t->text == S("(")) {
      next(p);
      p->pos_col = -1;
      p->no_do = false;
      Node *n;
      if (accept_sym(p, ")")) {
        n = mk(p, N_UNIT, t);
      } else if (is_sym(p, "←") || is_sym(p, "<-")) {
        next(p);
        n = mk(p, N_NESTED, t);
        n->a = parse_expr(p, 0);
        expect_sym(p, ")");
      } else {
        Node *e = parse_expr(p, 0);
        if (accept_sym(p, ":")) {
          n = mk(p, N_ASCRIBE, t);
          n->a = e;
          n->type = parse_type(p);
          expect_sym(p, ")");
        } else if (is_sym(p, ",")) {
          Vec items = {0};
          vpush(&items, e);
          while (accept_sym(p, ",")) vpush(&items, parse_expr(p, 0));
          expect_sym(p, ")");
          n = mk(p, N_TUPLE, t);
          n->list = items.v;
          n->n = items.n;
        } else {
          expect_sym(p, ")");
          n = e;
        }
      }
      p->pos_col = save_col;
      p->no_do = save_do;
      return n;
    }
    if (t->text == S("⟨") || t->text == S("#[")) {
      bool anon = t->text == S("⟨");
      next(p);
      p->pos_col = -1;
      p->no_do = false;
      Vec items = {0};
      const char *close = anon ? "⟩" : "]";
      if (!is_sym(p, close)) {
        do {
          vpush(&items, parse_expr(p, 0));
        } while (accept_sym(p, ","));
      }
      expect_sym(p, close);
      Node *n = mk(p, anon ? N_ANON : N_ARRLIT, t);
      n->list = items.v;
      n->n = items.n;
      p->pos_col = save_col;
      p->no_do = save_do;
      return n;
    }
    if (t->text == S("[")) { // range  [a:b]  [:b]  [a:b:c]
      next(p);
      p->pos_col = -1;
      p->no_do = false;
      Node *n = mk(p, N_RANGE, t);
      if (!is_sym(p, ":")) n->a = parse_expr(p, 0);
      if (!is_sym(p, ":")) err(p, peek(p), "list literals are not supported; expected a range [a:b]");
      next(p);
      n->b = parse_expr(p, 0);
      if (accept_sym(p, ":")) n->c = parse_expr(p, 0);
      expect_sym(p, "]");
      p->pos_col = save_col;
      p->no_do = save_do;
      return n;
    }
    if (t->text == S("{")) {
      next(p);
      p->pos_col = -1;
      p->no_do = false;
      Node *n = mk(p, N_STRUCT, t);
      Vec fields = {0};
      if (!is_sym(p, "}")) {
        bool plain = peek(p)->kind == T_IDENT &&
                     (tok_is(peek2(p), T_SYM, ":=") || tok_is(peek2(p), T_SYM, ",") || tok_is(peek2(p), T_SYM, "}"));
        if (!plain) {
          n->a = parse_expr(p, 0);
          expect_kw(p, "with");
        }
        while (!is_sym(p, "}")) {
          Token *ft = peek(p);
          Node *f = mk(p, N_FIELDINIT, ft);
          f->name = expect_ident(p);
          if (accept_sym(p, ":=")) {
            f->a = parse_expr(p, 0);
          } else { // field abbreviation { x } == { x := x }
            f->a = mk(p, N_IDENT, ft);
            f->a->name = f->name;
          }
          vpush(&fields, f);
          if (!accept_sym(p, ",")) break;
        }
      }
      expect_sym(p, "}");
      n->list = fields.v;
      n->n = fields.n;
      p->pos_col = save_col;
      p->no_do = save_do;
      return n;
    }
    if (t->text == S("←") || t->text == S("<-")) { // nested action without parentheses: ⟨← a, ← b⟩, {← e}
      next(p);
      Node *n = mk(p, N_NESTED, t);
      n->a = parse_expr(p, 0);
      return n;
    }
    if (t->text == S("!") || t->text == S("¬")) {
      next(p);
      Node *n = mk(p, N_UNOP, t);
      n->name = S("!");
      n->a = parse_expr(p, 40);
      return n;
    }
    if (t->text == S("~~~")) {
      next(p);
      Node *n = mk(p, N_UNOP, t);
      n->name = t->text;
      n->a = parse_expr(p, 1000);
      return n;
    }
    if (t->text == S("-")) {
      next(p);
      Node *n = mk(p, N_UNOP, t);
      n->name = t->text;
      n->a = parse_expr(p, 75);
      return n;
    }
    break;
  }
  }
  err(p, t, "expected an expression");
  return NULL;
}

// primary followed by tight postfix operators:  .field  .1  [i]!
static Node *parse_postfix(P *p) {
  Node *n = parse_primary(p);
  for (;;) {
    Token *t = peek(p);
    if (t->space_before) break;
    if (t->kind == T_DOTID) {
      next(p);
      Node *f = mk(p, N_FIELD, t);
      f->a = n;
      f->name = t->text;
      n = f;
    } else if (t->kind == T_DOTNUM) {
      next(p);
      Node *f = mk(p, N_FIELD, t);
      f->a = n;
      f->name = fmt("%lu", t->num);
      n = f;
    } else if (tok_is(t, T_SYM, "[")) {
      next(p);
      int save = p->pos_col;
      bool save_do = p->no_do;
      p->pos_col = -1;
      p->no_do = false;
      Node *ix = mk(p, N_INDEX, t);
      ix->a = n;
      ix->b = parse_expr(p, 0);
      expect_sym(p, "]");
      p->pos_col = save;
      p->no_do = save_do;
      if (!peek(p)->space_before && is_sym(p, "!")) {
        next(p);
        ix->flag = '!';
      } else {
        err(p, peek(p), "only the checked form a[i]! is supported for indexing");
      }
      n = ix;
    } else {
      break;
    }
  }
  return n;
}

static Node *parse_app(P *p) {
  Token *t = peek(p);
  Node *head = parse_postfix(p);
  Vec args = {0};
  for (;;) {
    Token *a = peek(p);
    if (!can_start_arg(p, a) || a->col <= p->pos_col) break;
    if (a->kind == T_KW) { // trailing `do` block
      vpush(&args, parse_primary(p));
      break;
    }
    vpush(&args, parse_postfix(p));
  }
  if (args.n == 0) return head;
  Node *n = mk(p, N_APP, t);
  n->a = head;
  n->list = args.v;
  n->n = args.n;
  return n;
}

static Node *parse_expr(P *p, int minprec) {
  Node *lhs = minprec >= 1000 ? parse_postfix(p) : parse_app(p);
  for (;;) {
    Token *t = peek(p);
    if (t->kind != T_SYM || t->col <= p->pos_col) break;
    if (minprec <= 0 && t->text == S("|>.")) { //  e |>.f args
      next(p);
      Token *ft = peek(p);
      Node *f = mk(p, N_FIELD, ft);
      f->a = lhs;
      f->name = expect_ident(p);
      Vec args = {0};
      while (can_start_arg(p, peek(p)) && peek(p)->col > p->pos_col && peek(p)->kind != T_KW)
        vpush(&args, parse_postfix(p));
      if (args.n) {
        Node *app = mk(p, N_APP, ft);
        app->a = f;
        app->list = args.v;
        app->n = args.n;
        lhs = app;
      } else {
        lhs = f;
      }
      continue;
    }
    if (minprec <= 10 && (t->text == S("<|") || t->text == S("$"))) { //  f <| e
      next(p);
      Node *arg = parse_expr(p, 10);
      if (lhs->kind == N_APP) {
        Vec args = {lhs->list, lhs->n, lhs->n};
        vpush(&args, arg);
        lhs->list = args.v;
        lhs->n = args.n;
      } else {
        Node *app = mk(p, N_APP, t);
        app->a = lhs;
        Vec args = {0};
        vpush(&args, arg);
        app->list = args.v;
        app->n = args.n;
        lhs = app;
      }
      continue;
    }
    const BinOp *op = NULL;
    for (int i = 0; binops[i].sym; i++)
      if (t->text == S(binops[i].sym)) op = &binops[i];
    if (!op || op->prec < minprec) break;
    next(p);
    Node *rhs = parse_expr(p, op->right ? op->prec : op->prec + 1);
    Node *n = mk(p, N_BINOP, t);
    n->name = t->text;
    n->a = lhs;
    n->b = rhs;
    lhs = n;
  }
  return lhs;
}

// --------------------------------------------------------------- do blocks
static bool block_end(P *p) {
  Token *t = peek(p);
  if (t->kind == T_EOF) return true;
  if (t->kind == T_KW)
    return t->text == S("else") || t->text == S("then") || t->text == S("with") || t->text == S("deriving") ||
           t->text == S("end");
  if (t->kind == T_SYM)
    return t->text == S(")") || t->text == S("]") || t->text == S("}") || t->text == S("⟩") || t->text == S(",") ||
           t->text == S("|");
  return false;
}

static Node *parse_block(P *p, Token *intro) {
  Token *first = peek(p);
  Node *n = mk(p, N_DO, first);
  Vec stmts = {0};
  bool save_do = p->no_do;
  p->no_do = false;
  if (first->line == intro->line) {
    vpush(&stmts, parse_stmt(p));
  } else {
    int col = first->col;
    if (col <= p->pos_col && p->pos_col >= 0 && col == 0) err(p, first, "expected an indented block");
    while (!block_end(p) && peek(p)->col == col) vpush(&stmts, parse_stmt(p));
    if (stmts.n == 0) err(p, first, "expected a statement");
  }
  p->no_do = save_do;
  n->list = stmts.v;
  n->n = stmts.n;
  return n;
}

static Node *parse_cond(P *p) {
  bool save = p->no_do;
  p->no_do = true;
  Node *c = parse_expr(p, 0);
  p->no_do = save;
  return c;
}

// `col` is the column an `else` must reach to belong to this `if`; chains of
// `else if` share the column of the first `if`.
static Node *parse_do_if(P *p, int col) {
  Token *t = expect_kw(p, "if");
  Node *n = mk(p, N_IF, t);
  n->flag = 1; // statement form
  n->a = parse_expr(p, 0);
  Token *th = expect_kw(p, "then");
  n->b = parse_block(p, th);
  if (is_kw(p, "else") && peek(p)->col >= col) {
    Token *el = next(p);
    if (is_kw(p, "if") && peek(p)->line == el->line) {
      Node *blk = mk(p, N_DO, peek(p));
      blk->list = xalloc(sizeof(Node *));
      blk->list[0] = parse_do_if(p, col);
      blk->n = 1;
      n->c = blk;
    } else {
      n->c = parse_block(p, el);
    }
  }
  return n;
}

static Node *parse_stmt(P *p) {
  Token *t = peek(p);
  int save = p->pos_col;
  p->pos_col = t->col;
  Node *n = NULL;
  if (t->kind == T_KW) {
    if (t->text == S("let")) {
      n = parse_let_head(p);
    } else if (t->text == S("for")) {
      next(p);
      n = mk(p, N_FOR, t);
      n->name = expect_ident(p);
      expect_kw(p, "in");
      n->a = parse_cond(p);
      Token *d = expect_kw(p, "do");
      n->b = parse_block(p, d);
    } else if (t->text == S("while")) {
      next(p);
      n = mk(p, N_WHILE, t);
      n->a = parse_cond(p);
      Token *d = expect_kw(p, "do");
      n->b = parse_block(p, d);
    } else if (t->text == S("repeat")) {
      next(p);
      n = mk(p, N_REPEAT, t);
      n->b = parse_block(p, t);
    } else if (t->text == S("unless")) {
      next(p);
      n = mk(p, N_UNLESS, t);
      n->a = parse_cond(p);
      Token *d = expect_kw(p, "do");
      n->b = parse_block(p, d);
    } else if (t->text == S("if")) {
      n = parse_do_if(p, t->col);
    } else if (t->text == S("match")) {
      n = parse_match(p, true);
      n->flag = 1;
    } else if (t->text == S("return")) {
      next(p);
      n = mk(p, N_RETURN, t);
      Token *a = peek(p);
      if (a->line == t->line && !block_end(p)) n->a = parse_expr(p, 0);
    } else if (t->text == S("break")) {
      next(p);
      n = mk(p, N_BREAK, t);
    } else if (t->text == S("continue")) {
      next(p);
      n = mk(p, N_CONTINUE, t);
    }
  } else if (t->kind == T_IDENT &&
             (tok_is(peek2(p), T_SYM, ":=") || tok_is(peek2(p), T_SYM, "←") || tok_is(peek2(p), T_SYM, "<-"))) {
    next(p);
    n = mk(p, N_ASSIGN, t);
    n->name = t->text;
    if (!accept_sym(p, ":=")) {
      next(p);
      n->flag |= 2;
    }
    n->a = parse_expr(p, 0);
  }
  if (!n) n = parse_expr(p, 0);
  accept_sym(p, ";");
  p->pos_col = save;
  return n;
}

// ------------------------------------------------------------ declarations
static const char *qualify(P *p, const char *name) {
  if (!p->ns[0]) return name;
  if (str_starts(name, "_root_.")) return intern(name + 7);
  return fmt("%s.%s", p->ns, name);
}

static void skip_command(P *p) {
  // skip to the next token that starts a line at column 0
  do {
    next(p);
  } while (peek(p)->kind != T_EOF && peek(p)->col != 0);
}

static void parse_params(P *p, Vec *out) {
  while (is_sym(p, "(")) {
    next(p);
    Vec names = {0};
    while (peek(p)->kind == T_IDENT) {
      Node *prm = mk(p, N_PARAM, peek(p));
      prm->name = next(p)->text;
      vpush(&names, prm);
    }
    if (names.n == 0) err(p, peek(p), "expected parameter name");
    expect_sym(p, ":");
    accept_sym(p, "@"); // borrow annotation  (x : @& T)
    if (is_sym(p, "&")) next(p);
    Node *ty = parse_type(p);
    expect_sym(p, ")");
    for (int i = 0; i < names.n; i++) {
      names.v[i]->type = ty;
      vpush(out, names.v[i]);
    }
  }
  if (is_sym(p, "{") || is_sym(p, "["))
    err(p, peek(p), "implicit and instance binders are not supported by leanc (functions must be monomorphic)");
}

static void stamp(P *p, Node *n) {
  n->ns = p->ns;
  n->opens = p->opens;
  n->nopens = p->nopens;
}

Module parse_module(const char *file, const char *src, u64 len) {
  TokenStream ts = lex(file, src, len, 1, 0);
  P P0 = {.file = file, .toks = ts.toks, .pos_col = 0, .ns = S("")};
  P *p = &P0;
  Vec decls = {0};
  Module m = {0};
  const char *ns_stack[64];
  int ns_depth = 0;
  const char *pending_extern = NULL;
  bool after_attr = false, pending_inline = false;

  while (peek(p)->kind != T_EOF) {
    Token *t = peek(p);
    if (t->col != 0 && !after_attr) err(p, t, "expected a top-level command at column 0");
    after_attr = false;
    p->pos_col = 0;
    p->no_do = false;

    if (is_sym(p, "@")) { // attributes
      next(p);
      expect_sym(p, "[");
      while (!is_sym(p, "]")) {
        Token *a = next(p);
        if (a->kind == T_EOF) err(p, a, "unterminated attribute");
        if (a->kind == T_IDENT && a->text == S("extern") && peek(p)->kind == T_STR)
          pending_extern = intern_n(peek(p)->str, peek(p)->slen);
        if (a->kind == T_IDENT && (a->text == S("inline") || a->text == S("always_inline"))) pending_inline = true;
      }
      next(p);
      after_attr = true;
      continue;
    }
    if (t->kind != T_KW) {
      if (is_sym(p, "#")) { // #eval, #check, ...
        skip_command(p);
        continue;
      }
      err(p, t, "expected a declaration");
    }
    const char *kw = t->text;
    while (kw == S("private") || kw == S("protected") || kw == S("partial") || kw == S("unsafe") ||
           kw == S("noncomputable")) {
      next(p);
      Token *d = peek(p);
      if (d->kind != T_KW) err(p, d, "expected a declaration after modifier");
      t = d;
      kw = d->text;
    }
    if (kw == S("import")) {
      next(p);
      const char *name = expect_ident(p);
      const char **ni = xalloc(sizeof(char *) * (u64)(m.nimports + 1));
      memcpy(ni, m.imports, sizeof(char *) * (u64)m.nimports);
      ni[m.nimports++] = name;
      m.imports = ni;
    } else if (kw == S("namespace") || kw == S("section") || kw == S("mutual")) {
      next(p);
      if (ns_depth == 64) err(p, t, "namespaces nested too deeply");
      ns_stack[ns_depth++] = p->ns;
      if (kw == S("namespace")) {
        const char *name = expect_ident(p);
        p->ns = p->ns[0] ? fmt("%s.%s", p->ns, name) : name;
      } else if (kw == S("section") && peek(p)->kind == T_IDENT && peek(p)->col != 0) {
        next(p);
      }
    } else if (kw == S("end")) {
      next(p);
      if (peek(p)->kind == T_IDENT && peek(p)->col != 0) next(p);
      if (ns_depth == 0) err(p, t, "'end' without matching namespace/section");
      p->ns = ns_stack[--ns_depth];
    } else if (kw == S("open")) {
      next(p);
      while (peek(p)->kind == T_IDENT && peek(p)->col != 0) {
        const char **no = xalloc(sizeof(char *) * (u64)(p->nopens + 1));
        memcpy(no, p->opens, sizeof(char *) * (u64)p->nopens);
        no[p->nopens++] = next(p)->text;
        p->opens = no;
      }
      if (is_kw(p, "in")) next(p);
    } else if (kw == S("def") || kw == S("abbrev") || kw == S("opaque")) {
      next(p);
      Node *d = mk(p, N_DEF, t);
      stamp(p, d);
      d->name = qualify(p, expect_ident(p));
      Vec params = {0};
      parse_params(p, &params);
      d->list = params.v;
      d->n = params.n;
      if (accept_sym(p, ":")) d->type = parse_type(p);
      d->str = pending_extern;
      pending_extern = NULL;
      if (pending_inline) d->flag |= 4;
      pending_inline = false;
      bool is_alias = params.n == 0 && ((d->type && d->type->kind == N_TYNAME && d->type->name == S("Type")) ||
                                        (!d->type && kw == S("abbrev")));
      if (kw == S("opaque")) {
        if (!d->str) fatal_at(file, t->line, t->col, "opaque declaration '%s' needs @[extern \"...\"]", d->name);
        if (peek(p)->kind != T_EOF && peek(p)->col != 0) skip_command(p);
      } else {
        expect_sym(p, ":=");
        if (is_alias) {
          d->kind = N_ALIAS;
          d->type = parse_type(p);
        } else if (d->str) {
          // extern with a reference implementation: the body is for the
          // official toolchain; leanc substitutes its intrinsic.
          p->pos--;
          skip_command(p);
        } else {
          if (!d->type) fatal_at(file, t->line, t->col, "definition '%s' needs an explicit return type", d->name);
          d->a = parse_expr(p, 0);
        }
      }
      vpush(&decls, d);
    } else if (kw == S("structure")) {
      next(p);
      Node *d = mk(p, N_STRUCTDECL, t);
      stamp(p, d);
      d->name = qualify(p, expect_ident(p));
      if (is_kw(p, "extends")) err(p, peek(p), "'extends' is not supported");
      expect_kw(p, "where");
      Vec fields = {0};
      while (peek(p)->kind == T_IDENT && peek(p)->col != 0) {
        if (tok_is(peek2(p), T_SYM, "::")) { // custom constructor name
          next(p);
          next(p);
          continue;
        }
        Vec names = {0};
        while (peek(p)->kind == T_IDENT) {
          Node *f = mk(p, N_PARAM, peek(p));
          f->name = next(p)->text;
          vpush(&names, f);
        }
        expect_sym(p, ":");
        Node *ty = parse_type(p);
        Node *dflt = NULL;
        if (accept_sym(p, ":=")) {
          int save = p->pos_col;
          p->pos_col = names.v[0]->col;
          dflt = parse_expr(p, 0);
          p->pos_col = save;
        }
        for (int i = 0; i < names.n; i++) {
          names.v[i]->type = ty;
          names.v[i]->a = dflt;
          vpush(&fields, names.v[i]);
        }
      }
      d->list = fields.v;
      d->n = fields.n;
      if (is_kw(p, "deriving")) skip_command(p);
      vpush(&decls, d);
    } else if (kw == S("inductive")) {
      next(p);
      Node *d = mk(p, N_INDDECL, t);
      stamp(p, d);
      d->name = qualify(p, expect_ident(p));
      expect_kw(p, "where");
      Vec ctors = {0};
      while (accept_sym(p, "|")) {
        Node *c = mk(p, N_CTORDECL, peek(p));
        c->name = expect_ident(p);
        Vec params = {0};
        parse_params(p, &params);
        if (is_sym(p, ":")) err(p, peek(p), "use binder syntax for constructor fields: | ctor (x : T)");
        c->list = params.v;
        c->n = params.n;
        vpush(&ctors, c);
      }
      d->list = ctors.v;
      d->n = ctors.n;
      if (is_kw(p, "deriving")) skip_command(p);
      vpush(&decls, d);
    } else if (kw == S("theorem") || kw == S("lemma") || kw == S("instance") || kw == S("example") ||
               kw == S("set_option") || kw == S("deriving") || kw == S("attribute") || kw == S("universe") ||
               kw == S("variable") || kw == S("export") || kw == S("axiom")) {
      // Proofs and instances are checked by the official toolchain and
      // erased here: they have no run-time content in this subset.
      pending_extern = NULL;
      skip_command(p);
    } else {
      err(p, t, "unsupported top-level command");
    }
  }
  m.decls = decls.v;
  m.ndecls = decls.n;
  return m;
}
