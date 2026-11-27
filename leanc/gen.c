// Code generator: typed IR -> x86-64 machine code, emitted byte by byte.
//
// Deliberately simple: every value is 8 bytes, expression results live in
// rax, locals live in the frame, temporaries on the machine stack. No
// register allocator, no assembler, no linker. The interesting part is the
// reference counting, which follows the ownership contract from live.c.
//
// Calling convention (private to leanc output): arguments are stored in an
// outgoing area on the stack, argument i at [rsp + 8*i] at the call; the
// callee owns them; the caller pops the area; result in rax; no register is
// preserved across a call.
//
// Heap object layout:
//   constructor object   [0] refcount  [8] tag    [16 + 8*i] field i
//   Array                [0] refcount  [8] size   [16] capacity  [24 + 8*i] element i
//   ByteArray / String   [0] refcount  [8] size   [16] capacity  [24 + i]   byte i
#include "leanc.h"

enum { RAX, RCX, RDX, RBX, RSP, RBP, RSI, RDI, R8, R9, R10, R11 };
enum { CC_O, CC_NO, CC_B, CC_AE, CC_E, CC_NE, CC_BE, CC_A };
enum { ALU_ADD, ALU_OR, ALU_ADC, ALU_SBB, ALU_AND, ALU_SUB, ALU_XOR, ALU_CMP };
enum { PANIC_BOUNDS = 1, PANIC_NAT_OVERFLOW, PANIC_MATCH, PANIC_OPTION, PANIC_SHIFT };

#define IMMORTAL (1ull << 62)

static Buf code, data;

// ------------------------------------------------------------------ labels
static int *label_pos;
static int nlabels, caplabels;
typedef struct {
  int at;    // offset of rel32 in code
  int label;
} Fixup;
static Fixup *fixups;
static int nfixups, capfixups;

static int new_label(void) {
  if (nlabels == caplabels) {
    int cap = caplabels ? caplabels * 2 : 1024;
    int *n = xalloc(sizeof(int) * (u64)cap);
    memcpy(n, label_pos, sizeof(int) * (u64)nlabels);
    label_pos = n;
    caplabels = cap;
  }
  label_pos[nlabels] = -1;
  return nlabels++ + 1; // 0 means "no label"
}
static u64 placed_at = ~0ull;
static void place(int l) {
  label_pos[l - 1] = (int)code.len;
  placed_at = code.len;
}
static void fix(int label) {
  if (nfixups == capfixups) {
    int cap = capfixups ? capfixups * 2 : 4096;
    Fixup *n = xalloc(sizeof(Fixup) * (u64)cap);
    memcpy(n, fixups, sizeof(Fixup) * (u64)nfixups);
    fixups = n;
    capfixups = cap;
  }
  fixups[nfixups].at = (int)code.len;
  fixups[nfixups++].label = label;
  buf_u32(&code, 0);
}

// ---------------------------------------------------------------- encoding
static void b1(int a) { buf_u8(&code, (u8)a); }

static void modrm_mem(int reg, int base, i64 disp) {
  int r = reg & 7, b = base & 7;
  int mod = (disp == 0 && b != 5) ? 0 : (disp >= -128 && disp <= 127) ? 1 : 2;
  b1(mod << 6 | r << 3 | b);
  if (b == 4) b1(0x24);
  if (mod == 1) b1((int)disp & 0xff);
  if (mod == 2) buf_u32(&code, (u32)disp);
}

// op reg, [base+disp]   (op1 < 0: single-byte opcode)
static void ins_mem(int w, int op0, int op1, int reg, int base, i64 disp) {
  int rex = 0x40 | (w ? 8 : 0) | ((reg >> 3) << 2) | (base >> 3);
  if (rex != 0x40) b1(rex);
  b1(op0);
  if (op1 >= 0) b1(op1);
  modrm_mem(reg, base, disp);
}

static void ins_rr(int w, int op0, int op1, int reg, int rm) {
  int rex = 0x40 | (w ? 8 : 0) | ((reg >> 3) << 2) | (rm >> 3);
  if (rex != 0x40) b1(rex);
  b1(op0);
  if (op1 >= 0) b1(op1);
  b1(0xC0 | (reg & 7) << 3 | (rm & 7));
}

// op reg, [base + index*scale + disp8]
static void ins_idx(int w, int op0, int op1, int reg, int base, int index, int scale, int disp) {
  int rex = 0x40 | (w ? 8 : 0) | ((reg >> 3) << 2) | ((index >> 3) << 1) | (base >> 3);
  if (rex != 0x40) b1(rex);
  b1(op0);
  if (op1 >= 0) b1(op1);
  b1(0x40 | (reg & 7) << 3 | 4);
  b1(scale << 6 | (index & 7) << 3 | (base & 7));
  b1(disp);
}

static void mov_rm(int reg, int base, i64 disp) { ins_mem(1, 0x8B, -1, reg, base, disp); }
static void mov_mr(int base, i64 disp, int reg) { ins_mem(1, 0x89, -1, reg, base, disp); }
static void mov_rr(int dst, int src) {
  if (dst != src) ins_rr(1, 0x89, -1, src, dst);
}
// Flag-preserving constant load.
static void mov_ri(int reg, u64 imm) {
  if (imm <= 0xffffffffull) {
    if (reg >> 3) b1(0x41);
    b1(0xB8 | (reg & 7));
    buf_u32(&code, (u32)imm);
  } else {
    b1(0x48 | (reg >> 3));
    b1(0xB8 | (reg & 7));
    buf_u64(&code, imm);
  }
}
static void store_imm(int base, i64 disp, u32 imm) {
  ins_mem(1, 0xC7, -1, 0, base, disp);
  buf_u32(&code, imm);
}
static void push_r(int reg) {
  if (reg >> 3) b1(0x41);
  b1(0x50 | (reg & 7));
}
static void pop_r(int reg) {
  if (reg >> 3) b1(0x41);
  b1(0x58 | (reg & 7));
}
static void push_imm(u32 imm) {
  b1(0x68);
  buf_u32(&code, imm);
}
static void alu_rr(int op, int dst, int src) { ins_rr(1, op << 3 | 1, -1, src, dst); }
static void alu_rm(int op, int reg, int base, i64 disp) { ins_mem(1, op << 3 | 3, -1, reg, base, disp); }
static void alu_ri(int op, int reg, i64 imm) {
  if (imm >= -128 && imm <= 127) {
    ins_rr(1, 0x83, -1, op, reg);
    b1((int)imm & 0xff);
  } else {
    ins_rr(1, 0x81, -1, op, reg);
    buf_u32(&code, (u32)imm);
  }
}
static void test_rr(int a, int b) { ins_rr(1, 0x85, -1, b, a); }
static void shift_ri(int w, int kind /*4 shl, 5 shr*/, int reg, int n) {
  ins_rr(w, 0xC1, -1, kind, reg);
  b1(n);
}
static void shift_cl(int w, int kind, int reg) { ins_rr(w, 0xD3, -1, kind, reg); }
static void setcc_movzx(int cc) { // al = cc; eax = zero-extended
  b1(0x0F), b1(0x90 | cc), b1(0xC0);
  b1(0x0F), b1(0xB6), b1(0xC0);
}
static void cmov(int cc, int dst, int src) { ins_rr(1, 0x0F, 0x40 | cc, dst, src); }
static void jmp(int label) {
  b1(0xE9);
  fix(label);
}
static void jcc(int cc, int label) {
  b1(0x0F), b1(0x80 | cc);
  fix(label);
}
static void call(int label) {
  b1(0xE8);
  fix(label);
}
static int jcc8(int cc) { // short forward jump, returns patch position
  b1(0x70 | cc), b1(0);
  return (int)code.len;
}
static int jmp8(void) {
  b1(0xEB), b1(0);
  return (int)code.len;
}
static void patch8(int at) {
  i64 d = (i64)code.len - at;
  if (d > 127) fatal("internal: short jump out of range");
  code.p[at - 1] = (char)d;
}
static void inc_mem(int base) { ins_mem(1, 0xFF, -1, 0, base, 0); }
static void dec_mem(int base) { ins_mem(1, 0xFF, -1, 1, base, 0); }
static void cmp_mem_imm8(int base, i64 disp, int imm) {
  ins_mem(1, 0x83, -1, 7, base, disp);
  b1(imm);
}
// eax <- zero-extended value of the given width
static void truncate(int reg, int bits) {
  if (bits == 32) ins_rr(0, 0x89, -1, reg, reg);
  else if (bits == 16) ins_rr(0, 0x0F, 0xB7, reg, reg);
  else if (bits == 8) {
    if (reg >= 4) fatal("internal: truncate8 on high register");
    ins_rr(0, 0x0F, 0xB6, reg, reg);
  }
}

// ------------------------------------------------------------- data section
static u64 str_addr(int id) {
  StrLit *s = &strlits[id];
  if (!s->addr) {
    while (data.len & 7) buf_u8(&data, 0);
    s->addr = DATA_BASE + data.len;
    buf_u64(&data, IMMORTAL);
    buf_u64(&data, (u64)s->len);
    buf_u64(&data, (u64)s->len);
    buf_put(&data, s->bytes, (u64)s->len);
    buf_u8(&data, 0);
  }
  return s->addr;
}

// Nullary constructors of boxed types are shared immortal objects: {rc, tag}.
static u64 tag_obj[256];
static u64 tag_addr(int tag) {
  if (tag >= 256) fatal("too many constructors");
  if (!tag_obj[tag]) {
    while (data.len & 7) buf_u8(&data, 0);
    tag_obj[tag] = DATA_BASE + data.len;
    buf_u64(&data, IMMORTAL);
    buf_u64(&data, (u64)tag);
  }
  return tag_obj[tag];
}

// --------------------------------------------------------- function context
static int nslots;
static Var *scope[4096];
static int nscope;

typedef struct {
  int label, kind, line;
} Stub;
static Stub stubs[4096];
static int nstubs;

typedef struct Loop {
  int brk, cont, depth;
  struct Loop *up;
} Loop;
static Loop *loop;

static i64 disp(Var *v) { return v->is_param ? 16 + 8 * v->slot : -8 * (i64)(v->slot + 1); }

// A local that is not a pointer lives in a register if it was given one (see assign_registers), otherwise
// in its frame slot. Reading into rax what was just read or written from rax, with nothing emitted since
// and no jump arriving in between, needs no instruction at all.
static Var *rax_var;
static u64 rax_at;
static void load_var(int reg, Var *v) {
  if (reg == RAX && rax_var == v && rax_at == code.len && placed_at != code.len) return;
  if (v->reg) mov_rr(reg, v->reg);
  else mov_rm(reg, RBP, disp(v));
  if (reg == RAX) rax_var = v, rax_at = code.len;
}
static void store_var(Var *v, int reg) {
  if (v->reg) mov_rr(v->reg, reg);
  else mov_mr(RBP, disp(v), reg);
  if (reg == RAX) rax_var = v, rax_at = code.len;
}
static void bind_slot(Var *v) {
  if (!v->is_param) v->slot = nslots++;
}
static void scope_push(Var *v) {
  if (!ty_is_ptr(v->type)) return;
  if (nscope == 4096) fatal("scope too deep");
  scope[nscope++] = v;
}

static int fn_label(Func *f) {
  if (!f->label) f->label = new_label();
  return f->label;
}
static int rt_label(const char *name) {
  Func *f = elab_find_func(name);
  if (!f || !f->queued) fatal("internal: runtime function %s not available", name);
  return fn_label(f);
}

static void panic_if(int cc, int kind, int line) {
  int l = 0;
  for (int i = 0; i < nstubs; i++)
    if (stubs[i].kind == kind && stubs[i].line == line) l = stubs[i].label;
  if (!l) {
    if (nstubs == 4096) fatal("function too large");
    l = new_label();
    stubs[nstubs].label = l;
    stubs[nstubs].kind = kind;
    stubs[nstubs++].line = line;
  }
  if (cc < 0) jmp(l);
  else jcc(cc, l);
}

// ------------------------------------------------------- reference counting
static Type **drop_queue;
static int ndrop, capdrop;

static int drop_label(Type *t) {
  t = ty_strip(t);
  if (!t->drop_label) {
    t->drop_label = new_label();
    if (ndrop == capdrop) {
      int cap = capdrop ? capdrop * 2 : 64;
      Type **n = xalloc(sizeof(Type *) * (u64)cap);
      memcpy(n, drop_queue, sizeof(Type *) * (u64)ndrop);
      drop_queue = n;
      capdrop = cap;
    }
    drop_queue[ndrop++] = t;
  }
  return t->drop_label;
}

// Drops the reference in `reg`. Clobbers everything except rax (if keep_rax).
static void release(int reg, Type *t, bool keep_rax) {
  dec_mem(reg);
  int skip = jcc8(CC_NE);
  if (keep_rax) push_r(RAX);
  push_r(reg);
  call(drop_label(t));
  pop_r(RCX);
  if (keep_rax) pop_r(RAX);
  patch8(skip);
}

static void release_var(Var *v, bool keep_rax) {
  mov_rm(RCX, RBP, disp(v));
  int skip = 0;
  if (v->moved) {
    test_rr(RCX, RCX);
    skip = jcc8(CC_E);
  }
  release(RCX, v->type, keep_rax);
  if (v->moved) patch8(skip);
}

// Emits releases for scope entries [depth, nscope) without popping them.
static void cleanup_to(int depth, bool keep_rax) {
  for (int i = nscope - 1; i >= depth; i--) release_var(scope[i], keep_rax);
}
static void scope_pop_to(int depth, bool keep_rax) {
  cleanup_to(depth, keep_rax);
  nscope = depth;
}

static bool has_value(Type *t) {
  t = ty_strip(t);
  return t->kind != K_UNIT && t->kind != K_NEVER;
}

// ------------------------------------------------------------- expressions
static void gen(Expr *e);

static u64 global_addr(Global *g) { return BSS_BASE + BSS_RT_SIZE + 16 * (u64)g->index; }
static int *global_labels;

// Ensures the constant is initialised; leaves its slot address in rcx.
static void global_ready(Global *g) {
  mov_ri(RCX, global_addr(g));
  ins_mem(0, 0x80, -1, 7, RCX, 0); // cmp byte [rcx], 0
  b1(0);
  int ok = jcc8(CC_NE);
  call(global_labels[g->index]);
  mov_ri(RCX, global_addr(g));
  patch8(ok);
}

// Loads a borrowed pointer (or scalar) reachable through a path into `reg`.
static void gen_path(Expr *e, int reg) {
  if (e->kind == E_LOCAL) {
    load_var(reg, e->var);
  } else if (e->kind == E_GLOBAL) {
    global_ready(e->glob);
    mov_rm(reg, RCX, 8);
  } else {
    gen_path(e->a, reg);
    mov_rm(reg, reg, 16 + 8 * (i64)e->num);
  }
}

static bool is_simple(Expr *e) {
  if (e->kind == E_INT) return e->num <= 0x7fffffffull;
  return e->kind == E_LOCAL && !ty_is_ptr(e->type);
}
static void alu_simple(int op, Expr *e) { // op rax, <simple>
  if (e->kind == E_INT) alu_ri(op, RAX, (i64)e->num);
  else if (e->var->reg) alu_rr(op, RAX, e->var->reg);
  else alu_rm(op, RAX, RBP, disp(e->var));
}

// Evaluates a and b into rax and rcx (b may be folded by the caller instead).
static void gen_two(Expr *a, Expr *b) {
  if (is_simple(b)) {
    gen(a);
    if (b->kind == E_INT) mov_ri(RCX, b->num);
    else load_var(RCX, b->var);
  } else {
    gen(a);
    push_r(RAX);
    gen(b);
    mov_rr(RCX, RAX);
    pop_r(RAX);
  }
}

static int cmp_cc(int op) {
  switch (op) {
  case OP_EQ: return CC_E;
  case OP_NE: return CC_NE;
  case OP_LT: return CC_B;
  case OP_LE: return CC_BE;
  case OP_GT: return CC_A;
  default: return CC_AE;
  }
}
static bool is_cmp(Expr *e) { return e->kind == E_OP && e->num >= OP_EQ && e->num <= OP_GE; }

static void gen_cmp_flags(Expr *e) {
  Expr *a = e->args[0], *b = e->args[1];
  if (is_simple(b)) {
    gen(a);
    alu_simple(ALU_CMP, b);
  } else {
    gen_two(a, b);
    alu_rr(ALU_CMP, RAX, RCX);
  }
}

// Jumps to `label` when e evaluates to `when`; falls through otherwise.
static void gen_branch(Expr *e, int label, bool when) {
  if (is_cmp(e)) {
    gen_cmp_flags(e);
    int cc = cmp_cc((int)e->num);
    jcc(when ? cc : cc ^ 1, label);
    return;
  }
  if (e->kind == E_OP && e->num == OP_LNOT) {
    gen_branch(e->args[0], label, !when);
    return;
  }
  if (e->kind == E_INT) {
    if ((e->num != 0) == when) jmp(label);
    return;
  }
  if (e->kind == E_IF && ty_strip(e->type) == ty_bool) {
    if (e->c->kind == E_INT && e->c->num == 0) { // a && b
      if (!when) {
        gen_branch(e->a, label, false);
        gen_branch(e->b, label, false);
      } else {
        int skip = new_label();
        gen_branch(e->a, skip, false);
        gen_branch(e->b, label, true);
        place(skip);
      }
      return;
    }
    if (e->b->kind == E_INT && e->b->num == 1) { // a || b
      if (when) {
        gen_branch(e->a, label, true);
        gen_branch(e->c, label, true);
      } else {
        int skip = new_label();
        gen_branch(e->a, skip, true);
        gen_branch(e->c, label, false);
        place(skip);
      }
      return;
    }
  }
  gen(e);
  test_rr(RAX, RAX);
  jcc(when ? CC_NE : CC_E, label);
}

static int log2_exact(u64 v) {
  if (!v || (v & (v - 1))) return -1;
  int n = 0;
  while (v >>= 1) n++;
  return n;
}

static void gen_arith(Expr *e) {
  int op = (int)e->num;
  Expr *a = e->args[0], *b = e->args[1];
  Type *t = ty_strip(e->type);
  bool nat = t->kind == K_NAT;
  int bits = ty_bits(t);
  switch (op) {
  case OP_ADD: case OP_AND: case OP_OR: case OP_XOR: {
    int alu = op == OP_ADD ? ALU_ADD : op == OP_AND ? ALU_AND : op == OP_OR ? ALU_OR : ALU_XOR;
    // (x >>> c) ||| (x <<< (w - c))  is a single rotate instruction
    if ((op == OP_OR || op == OP_XOR) && (bits == 32 || bits == 64) && a->kind == E_OP && b->kind == E_OP) {
      Expr *r = a->num == OP_SHR ? a : b, *l = a->num == OP_SHR ? b : a;
      if (r->num == OP_SHR && l->num == OP_SHL && r->args[1]->kind == E_INT && l->args[1]->kind == E_INT &&
          r->args[0]->kind == E_LOCAL && l->args[0]->kind == E_LOCAL && r->args[0]->var == l->args[0]->var &&
          r->args[1]->num > 0 && r->args[1]->num < (u64)bits && r->args[1]->num + l->args[1]->num == (u64)bits) {
        load_var(RAX, r->args[0]->var);
        ins_rr(bits == 64, 0xC1, -1, 1, RAX); // ror
        b1((int)r->args[1]->num);
        return;
      }
    }
    if (is_simple(b)) {
      gen(a);
      alu_simple(alu, b);
    } else if (is_simple(a)) {
      gen(b);
      alu_simple(alu, a);
    } else {
      gen_two(a, b);
      alu_rr(alu, RAX, RCX);
    }
    if (op == OP_ADD) {
      if (nat) panic_if(CC_B, PANIC_NAT_OVERFLOW, e->line);
      else truncate(RAX, bits);
    }
    return;
  }
  case OP_SUB:
    if (is_simple(b)) {
      gen(a);
      alu_simple(ALU_SUB, b);
    } else {
      gen_two(a, b);
      alu_rr(ALU_SUB, RAX, RCX);
    }
    if (nat) { // truncated subtraction: a - b = 0 when b > a
      mov_ri(RCX, 0);
      cmov(CC_B, RAX, RCX);
    } else {
      truncate(RAX, bits);
    }
    return;
  case OP_MUL:
    gen_two(a, b);
    if (nat) {
      ins_rr(1, 0xF7, -1, 4, RCX); // mul rcx
      panic_if(CC_B, PANIC_NAT_OVERFLOW, e->line);
    } else {
      ins_rr(1, 0x0F, 0xAF, RAX, RCX); // imul rax, rcx
      truncate(RAX, bits);
    }
    return;
  case OP_DIV: case OP_MOD: {
    if (b->kind == E_INT && log2_exact(b->num) >= 0) {
      gen(a);
      int k = log2_exact(b->num);
      if (op == OP_DIV) {
        if (k) shift_ri(1, 5, RAX, k);
      } else if (b->num - 1 <= 0x7fffffff) {
        alu_ri(ALU_AND, RAX, (i64)(b->num - 1));
      } else {
        mov_ri(RCX, b->num - 1);
        alu_rr(ALU_AND, RAX, RCX);
      }
      return;
    }
    gen_two(a, b);
    // Lean: x / 0 = 0 and x % 0 = x
    int zero = 0, end = 0;
    bool check = !(b->kind == E_INT && b->num != 0);
    if (check) {
      test_rr(RCX, RCX);
      zero = jcc8(CC_E);
    }
    mov_ri(RDX, 0);
    ins_rr(1, 0xF7, -1, 6, RCX); // div rcx
    if (op == OP_MOD) mov_rr(RAX, RDX);
    if (check) {
      if (op == OP_DIV) {
        end = jmp8();
        patch8(zero);
        mov_ri(RAX, 0);
        patch8(end);
      } else {
        patch8(zero);
      }
    }
    return;
  }
  case OP_SHL: case OP_SHR: {
    int kind = op == OP_SHL ? 4 : 5;
    if (b->kind == E_INT) {
      gen(a);
      u64 n = b->num;
      if (nat) {
        if (n >= 64) {
          if (op == OP_SHR) {
            mov_ri(RAX, 0);
          } else { // only 0 <<< n stays representable
            test_rr(RAX, RAX);
            panic_if(CC_NE, PANIC_NAT_OVERFLOW, e->line);
          }
        } else if (n) {
          if (op == OP_SHL) {
            mov_rr(RDX, RAX);
            shift_ri(1, 5, RDX, (int)(64 - n));
            test_rr(RDX, RDX);
            panic_if(CC_NE, PANIC_NAT_OVERFLOW, e->line);
          }
          shift_ri(1, kind, RAX, (int)n);
        }
      } else {
        n %= (u64)bits; // Lean: shift amount is taken modulo the width
        if (n) shift_ri(bits == 64, kind, RAX, (int)n);
        if (op == OP_SHL) truncate(RAX, bits);
      }
      return;
    }
    gen_two(a, b);
    if (nat) {
      if (op == OP_SHR) {
        shift_cl(1, 5, RAX);
        alu_ri(ALU_CMP, RCX, 64);
        mov_ri(RDX, 0);
        cmov(CC_AE, RAX, RDX);
      } else {
        alu_ri(ALU_CMP, RCX, 64);
        panic_if(CC_AE, PANIC_NAT_OVERFLOW, e->line);
        mov_rr(RDX, RAX);
        shift_cl(1, 4, RAX);
        mov_rr(RSI, RAX);
        shift_cl(1, 5, RSI);
        alu_rr(ALU_CMP, RSI, RDX);
        panic_if(CC_NE, PANIC_NAT_OVERFLOW, e->line);
      }
    } else {
      if (bits < 32) alu_ri(ALU_AND, RCX, bits - 1);
      shift_cl(bits == 64, kind, RAX);
      if (op == OP_SHL) truncate(RAX, bits);
    }
    return;
  }
  }
  fatal("internal: gen_arith op %d", op);
}

// Evaluates operands into an outgoing area: operand i at [rsp + 8*i].
// temps[i] is set when the operand is a borrowed temporary the caller must
// release after the operation.
static void gen_operands(Expr **args, int n, const char *modes, bool *temps) {
  if (n == 0) return;
  alu_ri(ALU_SUB, RSP, 8 * n);
  for (int i = 0; i < n; i++) {
    temps[i] = false;
    if (operand_deferred(args[i], modes[i])) continue;
    gen(args[i]);
    mov_mr(RSP, 8 * i, RAX);
    temps[i] = modes[i] == 'b' && ty_is_ptr(args[i]->type);
  }
  for (int i = 0; i < n; i++) {
    Expr *a = args[i];
    if (!operand_deferred(a, modes[i])) continue;
    if (a->kind == E_INT) {
      if (a->num <= 0x7fffffff) {
        store_imm(RSP, 8 * i, (u32)a->num);
        continue;
      }
      mov_ri(RAX, a->num);
    } else if (a->kind == E_STR) {
      mov_ri(RAX, str_addr((int)a->num));
    } else if (a->kind == E_LOCAL) {
      load_var(RAX, a->var);
      if (ty_is_ptr(a->type) && modes[i] == 'o') {
        if (a->move) store_imm(RBP, disp(a->var), 0);
        else inc_mem(RAX);
      }
    } else {
      gen_path(a, RAX);
    }
    mov_mr(RSP, 8 * i, RAX);
  }
}

// Releases borrowed temporaries left in the operand area, keeping rax.
static void release_temps(Expr **args, int n, bool *temps) {
  for (int i = 0; i < n; i++)
    if (temps[i]) {
      mov_rm(RCX, RSP, 8 * i);
      release(RCX, args[i]->type, true);
    }
}

static void gen_alloc_obj(int nfields, int tag) {
  push_imm((u32)(16 + 8 * nfields));
  call(rt_label("Rt.alloc"));
  pop_r(RCX);
  store_imm(RAX, 0, 1);
  store_imm(RAX, 8, (u32)tag);
}

// Borrowed read of an indexable/taggable object: evaluates `obj` so that a
// pointer to it ends up in rcx while rax holds the value of `idx` (if any).
// Returns true when rcx is an owned temporary that must be released.
static bool path_has_global(Expr *e) {
  while (e->kind == E_PROJ) e = e->a;
  return e->kind == E_GLOBAL;
}

static bool gen_borrow_with_index(Expr *obj, Expr *idx) {
  if (expr_is_path(obj)) {
    if (idx) gen(idx);
    bool save = idx && path_has_global(obj); // initialising a constant may call
    if (save) push_r(RAX);
    gen_path(obj, RCX);
    if (save) pop_r(RAX);
    return false;
  }
  gen(obj);
  if (idx) {
    push_r(RAX);
    gen(idx);
    pop_r(RCX);
  } else {
    mov_rr(RCX, RAX);
  }
  return true;
}

static void gen_intrin(Expr *e) {
  static const int sysregs[] = {RAX, RDI, RSI, RDX, R10, R8, R9};
  int which = (int)e->num2, n = e->nargs;
  char modes[16];
  bool temps[16];
  op_modes(e, modes);
  if (which == IN_PTR) {
    // The address of a heap object. Only meaningful while the caller keeps
    // the object alive in a variable, which is how rt/ and lib/Sys use it.
    Expr *a = e->args[0];
    if (!expr_is_path(a)) fatal("line %d: leanc_ptr needs a variable (the object must outlive the pointer)", e->line);
    gen_path(a, RAX);
    return;
  }
  if (which == IN_OFPTR || which == IN_DROPPED) {
    gen(e->args[0]);
    return;
  }
  gen_operands(e->args, n, modes, temps);
  switch (which) {
  case IN_SYSCALL:
    for (int i = 0; i < 7; i++) pop_r(sysregs[i]);
    b1(0x0F), b1(0x05);
    return;
  case IN_LOAD8: pop_r(RCX); ins_mem(0, 0x0F, 0xB6, RAX, RCX, 0); return;
  case IN_LOAD16: pop_r(RCX); ins_mem(0, 0x0F, 0xB7, RAX, RCX, 0); return;
  case IN_LOAD32: pop_r(RCX); ins_mem(0, 0x8B, -1, RAX, RCX, 0); return;
  case IN_LOAD64: pop_r(RCX); mov_rm(RAX, RCX, 0); return;
  case IN_STORE8: pop_r(RCX); pop_r(RAX); ins_mem(0, 0x88, -1, RAX, RCX, 0); return;
  case IN_STORE16: pop_r(RCX); pop_r(RAX); b1(0x66); ins_mem(0, 0x89, -1, RAX, RCX, 0); return;
  case IN_STORE32: pop_r(RCX); pop_r(RAX); ins_mem(0, 0x89, -1, RAX, RCX, 0); return;
  case IN_STORE64: pop_r(RCX); pop_r(RAX); mov_mr(RCX, 0, RAX); return;
  case IN_COPY: // dst src n
    pop_r(RDI), pop_r(RSI), pop_r(RCX);
    b1(0xF3), b1(0xA4);
    return;
  case IN_FILL: // dst byte n
    pop_r(RDI), pop_r(RAX), pop_r(RCX);
    b1(0xF3), b1(0xAA);
    return;
  case IN_MEMEQ: // a b n -> Bool
    pop_r(RSI), pop_r(RDI), pop_r(RCX);
    alu_rr(ALU_CMP, RAX, RAX); // ZF = 1 so that n = 0 compares equal
    b1(0xF3), b1(0xA6);
    setcc_movzx(CC_E);
    return;
  case IN_CAS32: // addr expected new -> previous value
    pop_r(RDI), pop_r(RAX), pop_r(RSI);
    b1(0xF0);
    ins_mem(0, 0x0F, 0xB1, RSI, RDI, 0);
    truncate(RAX, 32);
    return;
  case IN_CAS64:
    pop_r(RDI), pop_r(RAX), pop_r(RSI);
    b1(0xF0);
    ins_mem(1, 0x0F, 0xB1, RSI, RDI, 0);
    return;
  case IN_XADD64: // addr delta -> previous value
    pop_r(RDI), pop_r(RAX);
    b1(0xF0);
    ins_mem(1, 0x0F, 0xC1, RAX, RDI, 0);
    return;
  case IN_XCHG32: // addr value -> previous value
    pop_r(RDI), pop_r(RAX);
    ins_mem(0, 0x87, -1, RAX, RDI, 0);
    truncate(RAX, 32);
    return;
  case IN_PAUSE: b1(0xF3), b1(0x90); return;
  case IN_CALL: // address, then what it finds in rdi, rsi, rdx; it must keep rbx, rbp and r12-r15
    pop_r(RAX), pop_r(RDI), pop_r(RSI), pop_r(RDX);
    b1(0xFF), b1(0xD0);
    return;
  case IN_RDTSC:
    b1(0x0F), b1(0x31);
    shift_ri(1, 4, RDX, 32);
    alu_rr(ALU_OR, RAX, RDX);
    return;
  }
  fatal("internal: unknown intrinsic %d", which);
}

static void gen_op(Expr *e) {
  int op = (int)e->num, n = e->nargs;
  Type *t = ty_strip(e->type);
  char modes[64];
  bool temps[64];
  switch (op) {
  case OP_ADD: case OP_SUB: case OP_MUL: case OP_DIV: case OP_MOD: case OP_AND: case OP_OR: case OP_XOR:
  case OP_SHL: case OP_SHR:
    gen_arith(e);
    return;
  case OP_NOT:
    gen(e->args[0]);
    ins_rr(1, 0xF7, -1, 2, RAX);
    truncate(RAX, ty_bits(t));
    return;
  case OP_EQ: case OP_NE: case OP_LT: case OP_LE: case OP_GT: case OP_GE:
    gen_cmp_flags(e);
    setcc_movzx(cmp_cc(op));
    return;
  case OP_LNOT:
    gen(e->args[0]);
    alu_ri(ALU_XOR, RAX, 1);
    return;
  case OP_CONV: {
    gen(e->args[0]);
    int from = ty_bits(e->args[0]->type), to = ty_bits(t);
    if (to < from) truncate(RAX, to);
    return;
  }
  case OP_CAST:
    gen(e->args[0]);
    return;
  case OP_ARR_GET: case OP_BA_GET: {
    bool temp = gen_borrow_with_index(e->args[0], e->args[1]);
    alu_rm(ALU_CMP, RAX, RCX, 8);
    panic_if(CC_AE, PANIC_BOUNDS, e->line);
    if (op == OP_BA_GET) {
      ins_idx(0, 0x0F, 0xB6, RAX, RCX, RAX, 0, 24);
    } else {
      ins_idx(1, 0x8B, -1, RAX, RCX, RAX, 3, 24);
      if (ty_is_ptr(t)) inc_mem(RAX);
    }
    if (temp) release(RCX, e->args[0]->type, true);
    return;
  }
  case OP_ARR_SIZE: case OP_BA_SIZE: case OP_TAG: {
    bool temp = gen_borrow_with_index(e->args[0], NULL);
    mov_rm(RAX, RCX, 8);
    if (temp) release(RCX, e->args[0]->type, true);
    return;
  }
  case OP_OPT_GET: {
    bool temp = gen_borrow_with_index(e->args[0], NULL);
    cmp_mem_imm8(RCX, 8, 0);
    panic_if(CC_E, PANIC_OPTION, e->line);
    mov_rm(RAX, RCX, 16);
    if (ty_is_ptr(t)) inc_mem(RAX);
    if (temp) release(RCX, e->args[0]->type, true);
    return;
  }
  case OP_ARR_SET: case OP_BA_SET: {
    bool ba = op == OP_BA_SET;
    Type *et = ba ? ty_u8 : t->elem;
    op_modes(e, modes);
    gen_operands(e->args, 3, modes, temps); // [rsp] arr, [rsp+8] index, [rsp+16] value
    mov_rm(RAX, RSP, 0);
    cmp_mem_imm8(RAX, 0, 1);
    int fast = jcc8(CC_E);
    if (!ba) push_imm(ty_is_ptr(et));
    push_r(RAX);
    call(rt_label(ba ? "Rt.baUnique" : "Rt.arrUnique"));
    alu_ri(ALU_ADD, RSP, ba ? 8 : 16);
    patch8(fast);
    mov_rm(RDX, RSP, 8);
    alu_rm(ALU_CMP, RDX, RAX, 8);
    panic_if(CC_AE, PANIC_BOUNDS, e->line);
    mov_rm(RCX, RSP, 16);
    if (ba) {
      ins_idx(0, 0x88, -1, RCX, RAX, RDX, 0, 24);
    } else {
      if (ty_is_ptr(et)) ins_idx(1, 0x8B, -1, RSI, RAX, RDX, 3, 24);
      ins_idx(1, 0x89, -1, RCX, RAX, RDX, 3, 24);
    }
    alu_ri(ALU_ADD, RSP, 24);
    if (!ba && ty_is_ptr(et)) release(RSI, et, true);
    return;
  }
  case OP_ARR_PUSH: case OP_BA_PUSH: {
    bool ba = op == OP_BA_PUSH;
    Type *et = ba ? ty_u8 : t->elem;
    op_modes(e, modes);
    // reserve a third slot for the "elements are pointers" flag of the slow path
    alu_ri(ALU_SUB, RSP, 8);
    gen_operands(e->args, 2, modes, temps); // [rsp] arr, [rsp+8] value
    store_imm(RSP, 16, ty_is_ptr(et));
    mov_rm(RAX, RSP, 0);
    cmp_mem_imm8(RAX, 0, 1);
    int slow1 = jcc8(CC_NE);
    mov_rm(RDX, RAX, 8);
    alu_rm(ALU_CMP, RDX, RAX, 16);
    int slow2 = jcc8(CC_AE);
    mov_rm(RCX, RSP, 8);
    if (ba) ins_idx(0, 0x88, -1, RCX, RAX, RDX, 0, 24);
    else ins_idx(1, 0x89, -1, RCX, RAX, RDX, 3, 24);
    alu_ri(ALU_ADD, RDX, 1);
    mov_mr(RAX, 8, RDX);
    int done = jmp8();
    patch8(slow1);
    patch8(slow2);
    call(rt_label(ba ? "Rt.baPush" : "Rt.arrPush"));
    patch8(done);
    alu_ri(ALU_ADD, RSP, 24);
    return;
  }
  case OP_ARR_POP: {
    Type *et = t->elem;
    gen(e->args[0]);
    cmp_mem_imm8(RAX, 0, 1);
    int fast = jcc8(CC_E);
    push_imm(ty_is_ptr(et));
    push_r(RAX);
    call(rt_label("Rt.arrUnique"));
    alu_ri(ALU_ADD, RSP, 16);
    patch8(fast);
    mov_rm(RDX, RAX, 8);
    test_rr(RDX, RDX);
    int empty = jcc8(CC_E);
    alu_ri(ALU_SUB, RDX, 1);
    mov_mr(RAX, 8, RDX);
    if (ty_is_ptr(et)) {
      ins_idx(1, 0x8B, -1, RSI, RAX, RDX, 3, 24);
      release(RSI, et, true);
    }
    patch8(empty);
    return;
  }
  case OP_ARR_REPLICATE: {
    Type *et = t->elem;
    op_modes(e, modes);
    alu_ri(ALU_SUB, RSP, 8);
    gen_operands(e->args, 2, modes, temps);
    store_imm(RSP, 16, ty_is_ptr(et));
    call(rt_label("Rt.arrReplicate"));
    release_temps(e->args, 2, temps);
    alu_ri(ALU_ADD, RSP, 24);
    return;
  }
  case OP_ARR_EMPTY:
    gen(e->args[0]);
    push_r(RAX);
    call(rt_label("Rt.arrNew"));
    pop_r(RCX);
    return;
  case OP_PANIC:
    gen(e->args[0]);
    push_imm((u32)e->line);
    push_r(RAX);
    call(fn_label(e->fn));
    return;
  case OP_BA_LE: {
    // rcx = the array, rax = the index; in range: one load. Otherwise the runtime reads what bytes there are.
    int w = (int)e->num2;
    bool temp = gen_borrow_with_index(e->args[0], e->args[1]);
    mov_rm(RDX, RCX, 8);
    alu_ri(ALU_SUB, RDX, w);
    int slow1 = jcc8(CC_B);
    alu_rr(ALU_CMP, RAX, RDX);
    int slow2 = jcc8(CC_A);
    if (w == 8) ins_idx(1, 0x8B, -1, RAX, RCX, RAX, 0, 24);
    else if (w == 4) ins_idx(0, 0x8B, -1, RAX, RCX, RAX, 0, 24);
    else ins_idx(0, 0x0F, 0xB7, RAX, RCX, RAX, 0, 24);
    int done = jmp8();
    patch8(slow1);
    patch8(slow2);
    push_r(RCX);
    push_imm((u32)w);
    push_r(RAX);
    push_r(RCX);
    call(rt_label("Rt.baLe"));
    alu_ri(ALU_ADD, RSP, 24);
    pop_r(RCX);
    patch8(done);
    if (temp) release(RCX, e->args[0]->type, true);
    return;
  }
  case OP_BA_PUTLE: {
    int w = (int)e->num2;
    op_modes(e, modes);
    gen_operands(e->args, 3, modes, temps); // [rsp] array, [rsp+8] index, [rsp+16] value
    mov_rm(RAX, RSP, 0);
    cmp_mem_imm8(RAX, 0, 1);
    int fast = jcc8(CC_E);
    push_r(RAX);
    call(rt_label("Rt.baUnique"));
    alu_ri(ALU_ADD, RSP, 8);
    patch8(fast);
    mov_rm(RDX, RSP, 8);
    mov_rm(RSI, RAX, 8);
    alu_ri(ALU_SUB, RSI, w);
    panic_if(CC_B, PANIC_BOUNDS, e->line);
    alu_rr(ALU_CMP, RDX, RSI);
    panic_if(CC_A, PANIC_BOUNDS, e->line);
    mov_rm(RCX, RSP, 16);
    if (w == 2) b1(0x66);
    ins_idx(w == 8, 0x89, -1, RCX, RAX, RDX, 0, 24);
    alu_ri(ALU_ADD, RSP, 24);
    return;
  }
  case OP_HOT:
    gen(e->args[0]);
    return;
  case OP_MULHI:
    gen_two(e->args[0], e->args[1]);
    ins_rr(1, 0xF7, -1, 4, RCX); // mul rcx: rdx:rax = rax * rcx
    mov_rr(RAX, RDX);
    return;
  case OP_CPU: {
    push_r(RBX);
    mov_ri(RAX, 1);
    b1(0x0F), b1(0xA2);  // cpuid
    mov_rr(RSI, RCX);    // leaf 1: bit 27 = the OS uses XSAVE
    mov_ri(RAX, 7);
    mov_ri(RCX, 0);
    b1(0x0F), b1(0xA2);  // leaf 7: features in ebx and ecx
    mov_rr(RDI, RCX);
    ins_rr(0, 0x0F, 0xBA, 4, RSI), b1(27); // bt esi, 27
    int no_xsave = jcc8(CC_AE);
    mov_ri(RCX, 0);
    b1(0x0F), b1(0x01), b1(0xD0); // xgetbv: which state the OS saves
    alu_ri(ALU_AND, RAX, 0xE6);
    alu_ri(ALU_CMP, RAX, 0xE6);   // xmm, ymm, masks and both halves of zmm
    int saved = jcc8(CC_E);
    patch8(no_xsave);
    mov_ri(RAX, 0x3FDCFFFF);      // without them, no AVX-512: clear F, DQ, IFMA, BW, VL
    alu_rr(ALU_AND, RBX, RAX);
    patch8(saved);
    shift_ri(1, 4, RDI, 32);
    ins_rr(0, 0x89, -1, RBX, RAX); // mov eax, ebx
    alu_rr(ALU_OR, RAX, RDI);
    pop_r(RBX);
    return;
  }
  case OP_VEC: {
    // d = a (op) b on 64-byte slots of the array, in place. EVEX.512 with zmm0 (and zmm1), [rax + disp32].
    int which = (int)e->num2;
    u64 slot[8] = {0}, top = 0;
    bool scalar = which == V_SET32; // the last argument is a number computed at run time
    for (int i = 1; i < n - (scalar ? 1 : 0); i++) {
      if (e->args[i]->kind != E_INT) fatal("line %d: the slots of a vector operation must be literal numbers", e->line);
      slot[i - 1] = e->args[i]->num;
    }
    // (the last argument of some is a count or a selector, not a slot)
    bool count = which == V_ROR32 || which == V_SRL64 || which == V_SLL64 || which == V_XORROR32 || which == V_SHUF128;
    int nslots = n - 1 - (count || scalar ? 1 : 0);
    for (int i = 0; i < nslots; i++)
      if (slot[i] > top) top = slot[i];
    if (top > 4096 || (count && slot[nslots] > 255)) fatal("line %d: vector operand out of range", e->line);
    if (scalar) {
      gen(e->args[2]);
      push_r(RAX);
    }
    gen(e->args[0]);
    cmp_mem_imm8(RAX, 0, 1);
    int fast = jcc8(CC_E);
    push_r(RAX);
    call(rt_label("Rt.baUnique"));
    alu_ri(ALU_ADD, RSP, 8);
    patch8(fast);
    if (scalar) pop_r(RCX);
    mov_rm(RDX, RAX, 8);
    alu_ri(ALU_CMP, RDX, (i64)(64 * (top + 1)));
    panic_if(CC_B, PANIC_BOUNDS, e->line);
#define EVEX(mm, p1, opc, modrm, s) (b1(0x62), b1(0xF0 | (mm)), b1(p1), b1(0x48), b1(opc), b1(modrm), buf_u32(&code, (u32)(24 + 64 * (s))))
#define VLOAD0(s) EVEX(1, 0xFE, 0x6F, 0x80, s) /* vmovdqu64 zmm0, [slot] */
#define VLOAD1(s) EVEX(1, 0xFE, 0x6F, 0x88, s) /* vmovdqu64 zmm1, [slot] */
#define VSTORE0(s) EVEX(1, 0xFE, 0x7F, 0x80, s) /* vmovdqu64 [slot], zmm0 */
    switch (which) {
    case V_ADD32: VLOAD0(slot[1]); EVEX(1, 0x7D, 0xFE, 0x80, slot[2]); break;  // vpaddd
    case V_XOR: VLOAD0(slot[1]); EVEX(1, 0x7D, 0xEF, 0x80, slot[2]); break;    // vpxord
    case V_AND: VLOAD0(slot[1]); EVEX(1, 0x7D, 0xDB, 0x80, slot[2]); break;    // vpandd
    case V_ADD16: VLOAD0(slot[1]); EVEX(1, 0x7D, 0xFD, 0x80, slot[2]); break;  // vpaddw
    case V_SUB16: VLOAD0(slot[1]); EVEX(1, 0x7D, 0xF9, 0x80, slot[2]); break;  // vpsubw
    case V_ADD64: VLOAD0(slot[1]); EVEX(1, 0xFD, 0xD4, 0x80, slot[2]); break;  // vpaddq
    case V_ROR32: EVEX(1, 0x7D, 0x72, 0x80, slot[1]); b1((int)slot[2]); break; // vprord zmm0, [a], n   (/0)
    case V_SRL64: EVEX(1, 0xFD, 0x73, 0x90, slot[1]); b1((int)slot[2]); break; // vpsrlq zmm0, [a], n   (/2)
    case V_SLL64: EVEX(1, 0xFD, 0x73, 0xB0, slot[1]); b1((int)slot[2]); break; // vpsllq zmm0, [a], n   (/6)
    case V_MADD52LO: case V_MADD52HI: // zmm0 = acc + the low (high) 52 bits of a * b, per 64-bit lane
      VLOAD0(slot[1]);
      VLOAD1(slot[2]);
      EVEX(2, 0xF5, which == V_MADD52LO ? 0xB4 : 0xB5, 0x80, slot[3]);
      break;
    case V_QUARTER32: {
      // a, b, c, d in zmm0-3; the eight steps between registers; the message words straight from memory
#define VLOADR(r, s) EVEX(1, 0xFE, 0x6F, 0x80 | ((r) << 3), s)
#define VSTORER(r, s) EVEX(1, 0xFE, 0x7F, 0x80 | ((r) << 3), s)
#define VRR(opc, d, s) (b1(0x62), b1(0xF1), b1(0x05 | ((~(d) & 15) << 3)), b1(0x48), b1(opc), b1(0xC0 | ((d) << 3) | (s)))
#define VADDM(d, s) (b1(0x62), b1(0xF1), b1(0x05 | ((~(d) & 15) << 3)), b1(0x48), b1(0xFE), b1(0x80 | ((d) << 3)), buf_u32(&code, (u32)(24 + 64 * (s))))
#define VROR(d, n) (b1(0x62), b1(0xF1), b1(0x05 | ((~(d) & 15) << 3)), b1(0x48), b1(0x72), b1(0xC0 | (d)), b1(n))
      for (int r = 0; r < 4; r++) VLOADR(r, slot[r]);
      VRR(0xFE, 0, 1), VADDM(0, slot[4]); // a += b + mx
      VRR(0xEF, 3, 0), VROR(3, 16);       // d = (d ^ a) >>> 16
      VRR(0xFE, 2, 3);                    // c += d
      VRR(0xEF, 1, 2), VROR(1, 12);       // b = (b ^ c) >>> 12
      VRR(0xFE, 0, 1), VADDM(0, slot[5]); // a += b + my
      VRR(0xEF, 3, 0), VROR(3, 8);
      VRR(0xFE, 2, 3);
      VRR(0xEF, 1, 2), VROR(1, 7);
      for (int r = 1; r < 4; r++) VSTORER(r, slot[r]);
#undef VLOADR
#undef VSTORER
#undef VRR
#undef VADDM
#undef VROR
      break; // (zmm0, a, is stored below like every operation's result)
    }
    case V_MOVE: VLOAD0(slot[1]); break;
    case V_SET32: b1(0x62), b1(0xF2), b1(0x7D), b1(0x48), b1(0x7C), b1(0xC1); break; // vpbroadcastd zmm0, ecx
    case V_ADD32X3:
      VLOAD0(slot[1]);
      EVEX(1, 0x7D, 0xFE, 0x80, slot[2]);
      EVEX(1, 0x7D, 0xFE, 0x80, slot[3]);
      break;
    case V_XORROR32:
      VLOAD0(slot[1]);
      EVEX(1, 0x7D, 0xEF, 0x80, slot[2]);
      b1(0x62), b1(0xF1), b1(0x7D), b1(0x48), b1(0x72), b1(0xC0), b1((int)slot[3]); // vprord zmm0, zmm0, n
      break;
    case V_UNPCKLDQ: VLOAD0(slot[1]); EVEX(1, 0x7D, 0x62, 0x80, slot[2]); break;
    case V_UNPCKHDQ: VLOAD0(slot[1]); EVEX(1, 0x7D, 0x6A, 0x80, slot[2]); break;
    case V_UNPCKLQDQ: VLOAD0(slot[1]); EVEX(1, 0xFD, 0x6C, 0x80, slot[2]); break;
    case V_UNPCKHQDQ: VLOAD0(slot[1]); EVEX(1, 0xFD, 0x6D, 0x80, slot[2]); break;
    case V_SHUF128: VLOAD0(slot[1]); EVEX(3, 0x7D, 0x43, 0x80, slot[2]); b1((int)slot[3]); break; // vshufi32x4
    default: fatal("internal: vector operation %d", which);
    }
    VSTORE0(slot[0]);
#undef EVEX
#undef VLOAD0
#undef VLOAD1
#undef VSTORE0
    return;
  }
  case OP_RTCALL:
    op_modes(e, modes);
    gen_operands(e->args, n, modes, temps);
    call(fn_label(e->fn));
    release_temps(e->args, n, temps);
    if (n) alu_ri(ALU_ADD, RSP, 8 * n);
    return;
  case OP_INTRIN:
    gen_intrin(e);
    return;
  }
  fatal("internal: gen_op %d", op);
}

// ---- pattern matching
static void pat_load(Var *root, int *path, int depth, int reg) {
  load_var(reg, root);
  for (int i = 0; i < depth; i++) mov_rm(reg, reg, 16 + 8 * path[i]);
}

static void pat_test(Pat *p, Var *root, int *path, int depth, int fail) {
  if (p->kind == P_INT) {
    pat_load(root, path, depth, RAX);
    if (p->num <= 0x7fffffff) {
      alu_ri(ALU_CMP, RAX, (i64)p->num);
    } else {
      mov_ri(RCX, p->num);
      alu_rr(ALU_CMP, RAX, RCX);
    }
    jcc(CC_NE, fail);
  } else if (p->kind == P_CTOR) {
    if (ty_nctors(p->type) > 1) {
      pat_load(root, path, depth, RAX);
      cmp_mem_imm8(RAX, 8, (int)p->num);
      jcc(CC_NE, fail);
    }
    for (int i = 0; i < p->nsub; i++) {
      path[depth] = i;
      pat_test(p->sub[i], root, path, depth + 1, fail);
    }
  }
}

static void pat_bind(Pat *p, Var *root, int *path, int depth) {
  if (p->kind == P_VAR) {
    bind_slot(p->var);
    pat_load(root, path, depth, RAX);
    if (ty_is_ptr(p->type)) inc_mem(RAX);
    store_var(p->var, RAX);
    scope_push(p->var);
  } else if (p->kind == P_CTOR) {
    for (int i = 0; i < p->nsub; i++) {
      path[depth] = i;
      pat_bind(p->sub[i], root, path, depth + 1);
    }
  }
}

// A constructor pattern whose fields are all bound directly can take the
// fields out of a uniquely referenced scrutinee instead of copying them:
// destructuring a value you own is free.
static bool pat_can_steal(Pat *p) {
  if (p->kind != P_CTOR || p->nsub == 0) return false;
  for (int i = 0; i < p->nsub; i++) {
    Pat *s = p->sub[i];
    if (s->kind == P_VAR) continue;
    if (s->kind == P_WILD && !ty_is_ptr(s->type)) continue;
    return false;
  }
  return true;
}

static void gen_match(Expr *e) {
  int end = new_label();
  int path[32];
  bool value = has_value(e->type);
  for (int a = 0; a < e->narms; a++) {
    Arm *arm = &e->arms[a];
    int next = new_label();
    int depth = nscope;
    for (int i = 0; i < arm->npats; i++) pat_test(arm->pats[i], e->args[i]->var, path, 0, next);
    for (int i = 0; i < arm->npats; i++) {
      Pat *p = arm->pats[i];
      Var *root = e->args[i]->var;
      if (pat_can_steal(p)) {
        root->moved = true;
        mov_rm(RAX, RBP, disp(root));
        cmp_mem_imm8(RAX, 0, 1);
        int shared = new_label(), bound = new_label();
        jcc(CC_NE, shared);
        for (int k = 0; k < p->nsub; k++)
          if (p->sub[k]->kind == P_VAR) {
            bind_slot(p->sub[k]->var);
            mov_rm(RCX, RAX, 16 + 8 * k);
            store_var(p->sub[k]->var, RCX);
          }
        push_imm((u32)(16 + 8 * p->nsub));
        push_r(RAX);
        call(rt_label("Rt.free"));
        alu_ri(ALU_ADD, RSP, 16);
        store_imm(RBP, disp(root), 0);
        jmp(bound);
        place(shared);
        for (int k = 0; k < p->nsub; k++)
          if (p->sub[k]->kind == P_VAR) {
            mov_rm(RCX, RAX, 16 + 8 * k);
            if (ty_is_ptr(p->sub[k]->type)) inc_mem(RCX);
            store_var(p->sub[k]->var, RCX);
          }
        place(bound);
        for (int k = 0; k < p->nsub; k++)
          if (p->sub[k]->kind == P_VAR) scope_push(p->sub[k]->var);
      } else {
        pat_bind(p, root, path, 0);
      }
    }
    gen(arm->body);
    scope_pop_to(depth, value);
    jmp(end);
    place(next);
  }
  panic_if(-1, PANIC_MATCH, e->line);
  place(end);
}

static void gen(Expr *e) {
  switch (e->kind) {
  case E_INT: mov_ri(RAX, e->num); return;
  case E_UNIT: return;
  case E_STR: mov_ri(RAX, str_addr((int)e->num)); return;
  case E_LOCAL:
    load_var(RAX, e->var);
    if (ty_is_ptr(e->type)) {
      if (e->move) store_imm(RBP, disp(e->var), 0);
      else inc_mem(RAX);
    }
    return;
  case E_GLOBAL:
    global_ready(e->glob);
    mov_rm(RAX, RCX, 8);
    if (ty_is_ptr(e->type)) inc_mem(RAX);
    return;
  case E_CALL: {
    if (e->nargs > 60) fatal("line %d: too many arguments", e->line);
    char modes[64];
    bool temps[64];
    op_modes(e, modes);
    gen_operands(e->args, e->nargs, modes, temps);
    call(fn_label(e->fn));
    if (e->nargs) alu_ri(ALU_ADD, RSP, 8 * e->nargs);
    return;
  }
  case E_OP: gen_op(e); return;
  case E_CTOR: {
    int n = e->nargs;
    if (n == 0) {
      mov_ri(RAX, tag_addr((int)e->num));
      return;
    }
    if (n > 60) fatal("line %d: constructors with more than 60 fields are not supported", e->line);
    char modes[64];
    bool temps[64];
    op_modes(e, modes);
    gen_operands(e->args, n, modes, temps);
    gen_alloc_obj(n, (int)e->num);
    for (int i = 0; i < n; i++) {
      mov_rm(RCX, RSP, 8 * i);
      mov_mr(RAX, 16 + 8 * i, RCX);
    }
    alu_ri(ALU_ADD, RSP, 8 * n);
    return;
  }
  case E_ARRLIT: {
    int n = e->nargs;
    char modes[64];
    bool temps[64];
    if (n > 60) {
      // Long literals are filled in place, in the same order the operand
      // contract prescribes: compound elements first, then plain ones.
      push_imm((u32)n);
      call(rt_label("Rt.arrNew"));
      pop_r(RCX);
      store_imm(RAX, 8, (u32)n);
      push_r(RAX);
      for (int pass = 0; pass < 2; pass++)
        for (int i = 0; i < n; i++) {
          if (operand_deferred(e->args[i], 'o') != (pass == 1)) continue;
          gen(e->args[i]);
          mov_rm(RCX, RSP, 0);
          mov_mr(RCX, 24 + 8 * (i64)i, RAX);
        }
      pop_r(RAX);
      return;
    }
    op_modes(e, modes);
    gen_operands(e->args, n, modes, temps);
    push_imm((u32)n);
    call(rt_label("Rt.arrNew"));
    pop_r(RCX);
    store_imm(RAX, 8, (u32)n);
    for (int i = 0; i < n; i++) {
      mov_rm(RCX, RSP, 8 * i);
      mov_mr(RAX, 24 + 8 * i, RCX);
    }
    if (n) alu_ri(ALU_ADD, RSP, 8 * n);
    return;
  }
  case E_PROJ: {
    i64 off = 16 + 8 * (i64)e->num;
    if (expr_is_path(e->a)) {
      gen_path(e->a, RAX);
      mov_rm(RAX, RAX, off);
      if (ty_is_ptr(e->type)) inc_mem(RAX);
    } else {
      gen(e->a);
      mov_rr(RCX, RAX);
      mov_rm(RAX, RCX, off);
      if (ty_is_ptr(e->type)) inc_mem(RAX);
      release(RCX, e->a->type, true);
    }
    return;
  }
  case E_UPDATE: {
    int n = e->nargs;
    Type *t = ty_strip(e->type);
    int nf = ty_ctor_nfields(t, 0);
    if (nf > 64) fatal("line %d: structure update on a structure with more than 64 fields", e->line);
    Expr *ops[64];
    char modes[64];
    bool temps[64];
    for (int i = 0; i < n; i++) ops[i] = e->args[i], modes[i] = 'o';
    ops[n] = e->a;
    modes[n] = 'o';
    gen_operands(ops, n + 1, modes, temps); // [rsp+8i] value i, [rsp+8n] base
    mov_rm(RAX, RSP, 8 * n);
    cmp_mem_imm8(RAX, 0, 1);
    int fast = jcc8(CC_E);
    u64 mask = 0;
    for (int i = 0; i < nf; i++)
      if (ty_is_ptr(ty_ctor_field(t, 0, i))) mask |= 1ull << i;
    mov_ri(RCX, mask);
    push_r(RCX);
    push_imm((u32)nf);
    push_r(RAX);
    call(rt_label("Rt.objUnique"));
    alu_ri(ALU_ADD, RSP, 24);
    mov_mr(RSP, 8 * n, RAX);
    patch8(fast);
    for (int i = 0; i < n; i++) {
      i64 off = 16 + 8 * (i64)e->fields[i];
      mov_rm(RCX, RSP, 8 * i);
      if (ty_is_ptr(e->args[i]->type)) { // keep the old value for release
        mov_rm(RDX, RAX, off);
        mov_mr(RSP, 8 * i, RDX);
      }
      mov_mr(RAX, off, RCX);
    }
    for (int i = 0; i < n; i++)
      if (ty_is_ptr(e->args[i]->type)) {
        mov_rm(RCX, RSP, 8 * i);
        release(RCX, e->args[i]->type, false);
      }
    mov_rm(RAX, RSP, 8 * n);
    alu_ri(ALU_ADD, RSP, 8 * (n + 1));
    return;
  }
  case E_IF: {
    int els = new_label(), end = new_label();
    gen_branch(e->a, els, false);
    gen(e->b);
    if (e->c->kind == E_UNIT) {
      place(els);
      return;
    }
    jmp(end);
    place(els);
    gen(e->c);
    place(end);
    return;
  }
  case E_LET: {
    gen(e->a);
    bind_slot(e->var);
    store_var(e->var, RAX);
    int depth = nscope;
    scope_push(e->var);
    gen(e->b);
    scope_pop_to(depth, has_value(e->type));
    return;
  }
  case E_SEQ:
    for (int i = 0; i < e->nargs; i++) {
      gen(e->args[i]);
      if (i < e->nargs - 1 && ty_is_ptr(e->args[i]->type)) release(RAX, e->args[i]->type, false);
    }
    return;
  case E_ASSIGN: {
    // `x := x.set! i v` (or a wider store), with this the last use of the old x: if nobody else holds
    // the array, which is the usual case, the element is stored where it is and x is not touched.
    Expr *u = e->a;
    if (u->kind == E_OP && (u->num == OP_ARR_SET || u->num == OP_BA_SET || u->num == OP_BA_PUTLE) &&
        u->args[0]->kind == E_LOCAL && u->args[0]->var == e->var && u->args[0]->move &&
        !(u->num == OP_ARR_SET && ty_is_ptr(ty_strip(u->type)->elem))) {
      bool ba = u->num != OP_ARR_SET;
      int w = u->num == OP_BA_PUTLE ? (int)u->num2 : u->num == OP_BA_SET ? 1 : 8;
      Expr *idx = u->args[1], *val = u->args[2];
      if (is_simple(idx)) { // the value in rcx, the index in rdx
        gen(val);
        mov_rr(RCX, RAX);
        if (idx->kind == E_INT) mov_ri(RDX, idx->num);
        else load_var(RDX, idx->var);
      } else {
        gen(idx);
        push_r(RAX);
        gen(val);
        mov_rr(RCX, RAX);
        pop_r(RDX);
      }
      mov_rm(RAX, RBP, disp(e->var));
      cmp_mem_imm8(RAX, 0, 1);
      int fast = jcc8(CC_E);
      push_r(RCX); // shared after all: a copy of its own, which becomes x
      push_r(RDX);
      if (!ba) push_imm(0);
      push_r(RAX);
      call(rt_label(ba ? "Rt.baUnique" : "Rt.arrUnique"));
      alu_ri(ALU_ADD, RSP, ba ? 8 : 16);
      pop_r(RDX);
      pop_r(RCX);
      mov_mr(RBP, disp(e->var), RAX);
      patch8(fast);
      if (w == 1 || !ba) {
        alu_rm(ALU_CMP, RDX, RAX, 8);
        panic_if(CC_AE, PANIC_BOUNDS, e->line);
      } else {
        mov_rm(RSI, RAX, 8);
        alu_ri(ALU_SUB, RSI, w);
        panic_if(CC_B, PANIC_BOUNDS, e->line);
        alu_rr(ALU_CMP, RDX, RSI);
        panic_if(CC_A, PANIC_BOUNDS, e->line);
      }
      if (!ba) ins_idx(1, 0x89, -1, RCX, RAX, RDX, 3, 24);
      else if (w == 1) ins_idx(0, 0x88, -1, RCX, RAX, RDX, 0, 24);
      else {
        if (w == 2) b1(0x66);
        ins_idx(w == 8, 0x89, -1, RCX, RAX, RDX, 0, 24);
      }
      return;
    }
    gen(e->a);
    if (ty_is_ptr(e->var->type)) {
      mov_rm(RCX, RBP, disp(e->var));
      mov_mr(RBP, disp(e->var), RAX);
      int skip = 0;
      if (e->var->moved) {
        test_rr(RCX, RCX);
        skip = jcc8(CC_E);
      }
      release(RCX, e->var->type, false);
      if (e->var->moved) patch8(skip);
    } else {
      store_var(e->var, RAX);
    }
    return;
  }
  case E_LOOP: {
    Loop l = {new_label(), new_label(), nscope, loop};
    int head = new_label();
    place(head);
    if (e->a) gen_branch(e->a, l.brk, false);
    loop = &l;
    gen(e->b);
    loop = l.up;
    place(l.cont);
    if (e->c) gen(e->c);
    jmp(head);
    place(l.brk);
    return;
  }
  case E_BREAK:
    cleanup_to(loop->depth, false);
    jmp(loop->brk);
    return;
  case E_CONTINUE:
    cleanup_to(loop->depth, false);
    jmp(loop->cont);
    return;
  case E_RETURN:
    gen(e->a);
    cleanup_to(e->block->depth, has_value(e->block->type));
    jmp(e->block->label);
    return;
  case E_BLOCK: {
    Loop *save = loop;
    loop = NULL;
    e->label = new_label();
    e->depth = nscope;
    gen(e->a);
    place(e->label);
    loop = save;
    return;
  }
  case E_MATCH: gen_match(e); return;
  }
  fatal("internal: gen: unknown node %d", e->kind);
}

// ------------------------------------------------------------- functions
// How much each local is used, a use inside a loop counting eight times (and so on, loop within loop).
static void count_uses(Expr *e, u64 w) {
  if (!e) return;
  if ((e->kind == E_LOCAL || e->kind == E_LET || e->kind == E_ASSIGN) && e->var) e->var->uses += w;
  // `let x := Fast.hot ...`: the program says this one is worth a register
  if (e->kind == E_LET && e->a && e->a->kind == E_OP && e->a->num == OP_HOT) e->var->uses += 1ull << 40;
  u64 inner = e->kind == E_LOOP && w < 4096 ? w * 8 : w;
  count_uses(e->a, inner);
  count_uses(e->b, inner);
  count_uses(e->c, inner);
  for (int i = 0; i < e->nargs; i++) count_uses(e->args[i], w);
  for (int i = 0; i < e->narms; i++) count_uses(e->arms[i].body, w);
}

// The registers a function may keep for itself across calls (it saves and restores the ones it uses):
// the five busiest locals that are plain numbers get one each.
static const int keep_regs[] = {RBX, 12, 13, 14, 15};
static int assign_registers(Expr *body, Var **vars, int nvars) {
  for (int i = 0; i < nvars; i++) vars[i]->uses = 0, vars[i]->reg = 0;
  count_uses(body, 1);
  int n = 0;
  for (; n < 5; n++) {
    Var *best = NULL;
    for (int i = 0; i < nvars; i++) {
      Var *v = vars[i];
      if (v->reg || v->uses < 3 || ty_is_ptr(v->type) || !has_value(v->type)) continue;
      if (!best || v->uses > best->uses) best = v;
    }
    if (!best) break;
    best->reg = keep_regs[n];
  }
  return n;
}

static void gen_body(Expr *body, Var **params, int nparams, Global *store, Var **vars, int nvars) {
  int nkept = assign_registers(body, vars, nvars);
  b1(0x55);                   // push rbp
  mov_rr(RBP, RSP);
  ins_rr(1, 0x81, -1, 5, RSP); // sub rsp, imm32
  int frame_at = (int)code.len;
  buf_u32(&code, 0);
  // the caller's values of the registers this function keeps go to the first frame slots
  for (int i = 0; i < nkept; i++) mov_mr(RBP, -8 * (i64)(i + 1), keep_regs[i]);
  for (int i = 0; i < nparams; i++)
    if (params[i]->reg) mov_rm(params[i]->reg, RBP, disp(params[i]));
  nslots = nkept;
  nscope = 0;
  nstubs = 0;
  loop = NULL;
  rax_var = NULL;
  for (int i = 0; i < nparams; i++) scope_push(params[i]);
  gen(body);
  scope_pop_to(0, has_value(body->type));
  if (store) {
    mov_ri(RCX, global_addr(store));
    mov_mr(RCX, 8, RAX);
    store_imm(RCX, 0, 1);
  }
  for (int i = 0; i < nkept; i++) mov_rm(keep_regs[i], RBP, -8 * (i64)(i + 1));
  b1(0xC9), b1(0xC3); // leave; ret
  u32 frame = (u32)(8 * nslots + 15) & ~15u;
  memcpy(code.p + frame_at, &frame, 4);
  for (int i = 0; i < nstubs; i++) {
    place(stubs[i].label);
    push_imm((u32)stubs[i].line);
    push_imm((u32)stubs[i].kind);
    call(rt_label("Rt.panic"));
  }
}

static void gen_drop(Type *t) {
  place(t->drop_label);
  b1(0x55);
  mov_rr(RBP, RSP);
  int free_fn = rt_label("Rt.free");
  if (t->kind == K_STRING || t->kind == K_BYTES || t->kind == K_ARRAY) {
    bool ptr_elems = t->kind == K_ARRAY && ty_is_ptr(t->elem);
    if (ptr_elems) {
      push_imm(0); // [rbp-8] = index
      int head = new_label(), done = new_label();
      place(head);
      mov_rm(RCX, RBP, 16);
      mov_rm(RAX, RBP, -8);
      alu_rm(ALU_CMP, RAX, RCX, 8);
      jcc(CC_AE, done);
      ins_idx(1, 0x8B, -1, RAX, RCX, RAX, 3, 24);
      release(RAX, t->elem, false);
      inc_mem(RSP); // index++
      jmp(head);
      place(done);
    }
    mov_rm(RAX, RBP, 16);
    mov_rm(RCX, RAX, 16); // capacity
    if (t->kind == K_ARRAY) shift_ri(1, 4, RCX, 3);
    alu_ri(ALU_ADD, RCX, 24);
    push_r(RCX);
    push_r(RAX);
    call(free_fn);
  } else {
    int nc = ty_nctors(t);
    int done = new_label();
    for (int c = 0; c < nc; c++) {
      int nf = ty_ctor_nfields(t, c);
      if (nf == 0) continue; // nullary constructors are immortal
      int next = new_label();
      mov_rm(RAX, RBP, 16);
      if (nc > 1) {
        cmp_mem_imm8(RAX, 8, c);
        jcc(CC_NE, next);
      }
      for (int i = 0; i < nf; i++) {
        Type *ft = ty_ctor_field(t, c, i);
        if (!ty_is_ptr(ft)) continue;
        mov_rm(RAX, RBP, 16);
        mov_rm(RAX, RAX, 16 + 8 * i);
        release(RAX, ft, false);
      }
      push_imm((u32)(16 + 8 * nf));
      mov_rm(RAX, RBP, 16);
      push_r(RAX);
      call(free_fn);
      jmp(done);
      place(next);
    }
    place(done);
  }
  b1(0xC9), b1(0xC3);
}

void gen_program(Func *main_fn, Buf *out) {
  // reserve labels for constant initialisers
  global_labels = xalloc(sizeof(int) * (u64)(ngwork + 1));
  for (int i = 0; i < ngwork; i++) global_labels[gwork[i]->index] = new_label();

  // entry point
  mov_ri(RCX, BSS_BASE);
  mov_mr(RCX, 0, RSP); // initial stack pointer: argc, argv, envp
  call(fn_label(main_fn));
  if (ty_strip(main_fn->ret)->kind == K_UNIT) mov_ri(RDI, 0);
  else mov_rr(RDI, RAX);
  mov_ri(RAX, 231); // exit_group
  b1(0x0F), b1(0x05);

  // A function marked @[inline] is compiled on its own only if a call to it remains somewhere.
  bool *emitted = xalloc((u64)nwork + 1);
  for (int i = 0; i < nwork; i++) {
    Func *f = work[i];
    if (f->node && (f->node->flag & 4)) continue;
    emitted[i] = true;
    place(fn_label(f));
    Var **params = xalloc(sizeof(Var *) * (u64)(f->nparams + 1));
    for (int k = 0; k < f->nparams; k++) params[k] = f->vars[k];
    gen_body(f->body, params, f->nparams, NULL, f->vars, f->nvars);
  }
  for (int i = 0; i < ngwork; i++) {
    place(global_labels[gwork[i]->index]);
    gen_body(gwork[i]->init, NULL, 0, gwork[i], gwork[i]->vars, gwork[i]->nvars);
  }
  for (bool again = true; again;) {
    again = false;
    for (int i = 0; i < nwork; i++) {
      Func *f = work[i];
      if (emitted[i] || !f->label) continue;
      emitted[i] = again = true;
      place(f->label);
      Var **params = xalloc(sizeof(Var *) * (u64)(f->nparams + 1));
      for (int k = 0; k < f->nparams; k++) params[k] = f->vars[k];
      gen_body(f->body, params, f->nparams, NULL, f->vars, f->nvars);
    }
  }
  for (int i = 0; i < ndrop; i++) gen_drop(drop_queue[i]);

  u64 code_base = TEXT_BASE + 0x1000;
  if (opt_map) {
    // one line per function, in address order: where it starts, and its name
    for (int i = 0; i < nwork; i++)
      if (emitted[i]) buf_fmt(&map_out, "%lx %s\n", code_base + (u64)label_pos[work[i]->label - 1], work[i]->name);
    for (int i = 0; i < ngwork; i++)
      buf_fmt(&map_out, "%lx (constant %d)\n", code_base + (u64)label_pos[global_labels[gwork[i]->index] - 1], i);
    buf_fmt(&map_out, "%lx (end)\n", code_base + (u64)code.len);
  }
  for (int i = 0; i < nfixups; i++) {
    int target = label_pos[fixups[i].label - 1];
    if (target < 0) fatal("internal: unresolved label %d", fixups[i].label);
    int rel = target - (fixups[i].at + 4);
    memcpy(code.p + fixups[i].at, &rel, 4);
  }

  // ---- ELF64 executable: headers, text (RX), data (RW), bss (RW)
  u64 bss_size = BSS_RT_SIZE + 16 * (u64)nglobals + 0x1000;
  u64 text_filesz = 0x1000 + code.len;
  u64 data_off = (text_filesz + 0xfff) & ~0xfffull;
  Buf *o = out;
  static const u8 ident[16] = {0x7f, 'E', 'L', 'F', 2, 1, 1, 0};
  buf_put(o, ident, 16);
  u16 hdr16[] = {2 /*ET_EXEC*/, 62 /*x86-64*/};
  buf_put(o, hdr16, 4);
  buf_u32(o, 1);
  buf_u64(o, code_base); // entry
  buf_u64(o, 64);        // phoff
  buf_u64(o, 0);         // shoff
  buf_u32(o, 0);
  u16 sizes[] = {64, 56, 4, 64, 0, 0};
  buf_put(o, sizes, 12);
  struct {
    u32 type, flags;
    u64 off, vaddr, paddr, filesz, memsz, align;
  } ph[4] = {
      {1, 5, 0, TEXT_BASE, TEXT_BASE, text_filesz, text_filesz, 0x1000},
      {1, 6, data_off, DATA_BASE, DATA_BASE, data.len, data.len, 0x1000},
      {1, 6, 0, BSS_BASE, BSS_BASE, 0, bss_size, 0x1000},
      {0x6474e551 /*GNU_STACK*/, 6, 0, 0, 0, 0, 0, 16},
  };
  buf_put(o, ph, sizeof ph);
  while (o->len < 0x1000) buf_u8(o, 0);
  buf_put(o, code.p, code.len);
  while (o->len < data_off) buf_u8(o, 0);
  buf_put(o, data.p, data.len);
}
