// Type representation. Types are hash-consed: pointer equality is type equality.
#include "leanc.h"

static Type *mk_prim(int kind, const char *name) {
  Type *t = xalloc(sizeof(Type));
  t->kind = kind;
  t->name = name;
  return t;
}

Type *ty_nat, *ty_u8, *ty_u16, *ty_u32, *ty_u64, *ty_usize, *ty_bool, *ty_char, *ty_unit, *ty_string, *ty_bytes,
    *ty_never;
static Type *derived;

void types_init(void) {
  ty_nat = mk_prim(K_NAT, "Nat");
  ty_u8 = mk_prim(K_U8, "UInt8");
  ty_u16 = mk_prim(K_U16, "UInt16");
  ty_u32 = mk_prim(K_U32, "UInt32");
  ty_u64 = mk_prim(K_U64, "UInt64");
  ty_usize = mk_prim(K_USIZE, "USize");
  ty_bool = mk_prim(K_BOOL, "Bool");
  ty_char = mk_prim(K_CHAR, "Char");
  ty_unit = mk_prim(K_UNIT, "Unit");
  ty_string = mk_prim(K_STRING, "String");
  ty_bytes = mk_prim(K_BYTES, "ByteArray");
  ty_never = mk_prim(K_NEVER, "<never>");
}

static Type *derive(int kind, Type *elem, Type *a, Type *b) {
  for (Type *t = derived; t; t = t->next)
    if (t->kind == kind && t->elem == elem && t->a == a && t->b == b) return t;
  Type *t = xalloc(sizeof(Type));
  t->kind = kind;
  t->elem = elem;
  t->a = a;
  t->b = b;
  t->next = derived;
  derived = t;
  return t;
}

Type *ty_array(Type *elem) { return derive(K_ARRAY, elem, NULL, NULL); }
Type *ty_option(Type *elem) { return derive(K_OPTION, elem, NULL, NULL); }
Type *ty_prod(Type *a, Type *b) { return derive(K_PROD, NULL, a, b); }

Type *ty_io(Type *t) {
  if (t->io) return t;
  if (!t->io_type) {
    Type *w = xalloc(sizeof(Type));
    w->kind = K_IO;
    w->io = true;
    w->elem = t; // base type
    t->io_type = w;
  }
  return t->io_type;
}

Type *ty_strip(Type *t) { return t && t->io ? t->elem : t; }

bool ty_is_ptr(Type *t) {
  t = ty_strip(t);
  return t->kind >= K_STRING && t->kind <= K_IND;
}

bool ty_is_int(Type *t) {
  t = ty_strip(t);
  return t->kind >= K_NAT && t->kind <= K_USIZE;
}

int ty_bits(Type *t) {
  switch (ty_strip(t)->kind) {
  case K_U8: return 8;
  case K_U16: return 16;
  case K_U32: case K_CHAR: return 32;
  case K_BOOL: return 1;
  default: return 64;
  }
}

const char *ty_name(Type *t) {
  if (!t) return "?";
  if (t->io) return fmt("IO %s", ty_name(t->elem));
  switch (t->kind) {
  case K_ARRAY: return fmt("Array %s", ty_name(t->elem));
  case K_OPTION: return fmt("Option %s", ty_name(t->elem));
  case K_PROD: return fmt("(%s × %s)", ty_name(t->a), ty_name(t->b));
  case K_STRUCT: case K_IND: case K_ENUM: return t->decl->name;
  default: return t->name;
  }
}

int ty_nctors(Type *t) {
  t = ty_strip(t);
  switch (t->kind) {
  case K_OPTION: return 2;
  case K_PROD: return 1;
  case K_STRUCT: case K_IND: case K_ENUM: return t->decl->nctors;
  case K_BOOL: return 2;
  }
  return 0;
}

int ty_ctor_nfields(Type *t, int tag) {
  t = ty_strip(t);
  switch (t->kind) {
  case K_OPTION: return tag;
  case K_PROD: return 2;
  case K_STRUCT: case K_IND: return t->decl->ctors[tag].nfields;
  }
  return 0;
}

Type *ty_ctor_field(Type *t, int tag, int i) {
  t = ty_strip(t);
  switch (t->kind) {
  case K_OPTION: return t->elem;
  case K_PROD: return i == 0 ? t->a : t->b;
  case K_STRUCT: case K_IND: return t->decl->ctors[tag].fields[i].type;
  }
  return NULL;
}
