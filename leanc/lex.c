// Lexer for the Lean 4 subset.
#include "leanc.h"

static const char *keywords[] = {
    "def", "partial", "private", "protected", "structure", "inductive", "where", "namespace",
    "end", "open", "import", "if", "then", "else", "match", "with", "let", "mut", "do", "for",
    "in", "while", "return", "break", "continue", "fun", "theorem", "instance", "abbrev",
    "opaque", "deriving", "unless", "repeat", "mutual", "section", "example", "unsafe",
    "noncomputable", "extends", "class", "set_option", "attribute", "universe", "variable",
    "export", "macro", "syntax", "lemma", "axiom", "at", "have", "show", "from", "by", NULL};

// Longest-match punctuation table (UTF-8 aware).
static const char *symbols[] = {
    "<<<", ">>>", "&&&", "|||", "^^^", "~~~", "|>.", ":=", "=>", "->", "<-", "&&", "||", "==",
    "!=", "<=", ">=", "++", "::", "..", "#[", "|>", "<|", "←", "→", "⟨", "⟩", "×", "≠", "≤",
    "≥", "∧", "∨", "¬", "↦", "(", ")", "[", "]", "{", "}", ",", ":", ";", "|", "@", "#", "+",
    "-", "*", "/", "%", "<", ">", "=", "!", ".", "?", "^", "$", "&", NULL};

static bool is_id_start(u8 c) {
  return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_';
}
static bool is_digit(u8 c) { return c >= '0' && c <= '9'; }
static bool is_id_char(u8 c) { return is_id_start(c) || is_digit(c) || c == '\''; }

typedef struct {
  const char *file, *src;
  u64 len, pos;
  int line, col;
  Token *toks;
  int ntoks, cap;
} Lexer;

static void advance(Lexer *lx, u64 n) {
  for (u64 i = 0; i < n; i++) {
    u8 c = (u8)lx->src[lx->pos++];
    if (c == '\n') {
      lx->line++;
      lx->col = 0;
    } else if ((c & 0xC0) != 0x80) { // count code points, not bytes
      lx->col++;
    }
  }
}

static Token *push(Lexer *lx, int kind, int line, int col, bool space) {
  if (lx->ntoks == lx->cap) {
    int cap = lx->cap ? lx->cap * 2 : 1024;
    Token *t = xalloc(sizeof(Token) * (u64)cap);
    memcpy(t, lx->toks, sizeof(Token) * (u64)lx->ntoks);
    lx->toks = t;
    lx->cap = cap;
  }
  Token *t = &lx->toks[lx->ntoks++];
  memset(t, 0, sizeof *t);
  t->kind = kind;
  t->line = line;
  t->col = col;
  t->space_before = space;
  return t;
}

static int hexval(u8 c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  return -1;
}

static void put_utf8(Buf *b, u32 cp) {
  if (cp < 0x80) {
    buf_u8(b, (u8)cp);
  } else if (cp < 0x800) {
    buf_u8(b, (u8)(0xC0 | (cp >> 6)));
    buf_u8(b, (u8)(0x80 | (cp & 0x3F)));
  } else if (cp < 0x10000) {
    buf_u8(b, (u8)(0xE0 | (cp >> 12)));
    buf_u8(b, (u8)(0x80 | ((cp >> 6) & 0x3F)));
    buf_u8(b, (u8)(0x80 | (cp & 0x3F)));
  } else {
    buf_u8(b, (u8)(0xF0 | (cp >> 18)));
    buf_u8(b, (u8)(0x80 | ((cp >> 12) & 0x3F)));
    buf_u8(b, (u8)(0x80 | ((cp >> 6) & 0x3F)));
    buf_u8(b, (u8)(0x80 | (cp & 0x3F)));
  }
}

// Reads one escape sequence after a backslash; returns code point.
static u32 read_escape(Lexer *lx) {
  u8 c = (u8)lx->src[lx->pos];
  advance(lx, 1);
  switch (c) {
  case 'n': return '\n';
  case 't': return '\t';
  case 'r': return '\r';
  case '0': return 0;
  case '\\': return '\\';
  case '"': return '"';
  case '\'': return '\'';
  case 'x': {
    int a = hexval((u8)lx->src[lx->pos]), b = hexval((u8)lx->src[lx->pos + 1]);
    if (a < 0 || b < 0) fatal_at(lx->file, lx->line, lx->col, "bad \\x escape");
    advance(lx, 2);
    return (u32)(a * 16 + b);
  }
  case 'u': {
    if (lx->src[lx->pos] != '{') fatal_at(lx->file, lx->line, lx->col, "bad \\u escape");
    advance(lx, 1);
    u32 v = 0;
    while (hexval((u8)lx->src[lx->pos]) >= 0) {
      v = v * 16 + (u32)hexval((u8)lx->src[lx->pos]);
      advance(lx, 1);
    }
    if (lx->src[lx->pos] != '}') fatal_at(lx->file, lx->line, lx->col, "bad \\u escape");
    advance(lx, 1);
    return v;
  }
  }
  fatal_at(lx->file, lx->line, lx->col, "unknown escape '\\%c'", c);
}

static u32 read_codepoint(Lexer *lx) {
  u8 c = (u8)lx->src[lx->pos];
  int n = c < 0x80 ? 1 : c < 0xE0 ? 2 : c < 0xF0 ? 3 : 4;
  u32 cp = n == 1 ? c : (u32)(c & (0xFF >> (n + 1)));
  for (int i = 1; i < n; i++) cp = (cp << 6) | ((u8)lx->src[lx->pos + (u64)i] & 0x3F);
  advance(lx, (u64)n);
  return cp;
}

TokenStream lex(const char *file, const char *src, u64 len, int line0, int col0) {
  Lexer L = {.file = file, .src = src, .len = len, .line = line0, .col = col0};
  Lexer *lx = &L;
  bool space = true;
  while (lx->pos < len) {
    u8 c = (u8)src[lx->pos];
    u8 c1 = lx->pos + 1 < len ? (u8)src[lx->pos + 1] : 0;
    if (c == ' ' || c == '\t' || c == '\n' || c == '\r') {
      advance(lx, 1);
      space = true;
      continue;
    }
    if (c == '-' && c1 == '-') {
      while (lx->pos < len && src[lx->pos] != '\n') advance(lx, 1);
      space = true;
      continue;
    }
    if (c == '/' && c1 == '-') {
      int depth = 0;
      int sl = lx->line, sc = lx->col;
      do {
        if (lx->pos + 1 >= len) fatal_at(file, sl, sc, "unterminated comment");
        if (src[lx->pos] == '/' && src[lx->pos + 1] == '-') {
          depth++;
          advance(lx, 2);
        } else if (src[lx->pos] == '-' && src[lx->pos + 1] == '/') {
          depth--;
          advance(lx, 2);
        } else {
          advance(lx, 1);
        }
      } while (depth > 0);
      space = true;
      continue;
    }
    int line = lx->line, col = lx->col;

    // interpolated string  s!"..."
    if (c == 's' && c1 == '!' && lx->pos + 2 < len && src[lx->pos + 2] == '"') {
      advance(lx, 3);
      u64 start = lx->pos;
      int depth = 0;
      while (lx->pos < len && (src[lx->pos] != '"' || depth > 0)) {
        if (src[lx->pos] == '\\' && depth == 0) advance(lx, 1);
        else if (src[lx->pos] == '{') depth++;
        else if (src[lx->pos] == '}') depth--;
        advance(lx, 1);
      }
      if (lx->pos >= len) fatal_at(file, line, col, "unterminated string");
      Token *t = push(lx, T_INTERP, line, col, space);
      t->str = intern_n(src + start, (int)(lx->pos - start));
      t->slen = (int)(lx->pos - start);
      advance(lx, 1);
      space = false;
      continue;
    }

    if (is_id_start(c)) {
      u64 start = lx->pos;
      for (;;) {
        while (lx->pos < len && is_id_char((u8)src[lx->pos])) advance(lx, 1);
        // trailing ! or ? belongs to the identifier (get!, back?), but "!=" does not
        if (lx->pos < len && (src[lx->pos] == '!' || src[lx->pos] == '?') &&
            !(lx->pos + 1 < len && src[lx->pos + 1] == '=')) {
          advance(lx, 1);
        }
        // a.b continues the identifier
        if (lx->pos + 1 < len && src[lx->pos] == '.' && is_id_start((u8)src[lx->pos + 1])) {
          advance(lx, 1);
          continue;
        }
        break;
      }
      const char *text = intern_n(src + start, (int)(lx->pos - start));
      int kind = T_IDENT;
      for (int i = 0; keywords[i]; i++)
        if (text == intern(keywords[i])) kind = T_KW;
      Token *t = push(lx, kind, line, col, space);
      t->text = text;
      space = false;
      continue;
    }

    if (is_digit(c)) {
      u64 v = 0;
      if (c == '0' && (c1 == 'x' || c1 == 'X')) {
        advance(lx, 2);
        while (lx->pos < len && (hexval((u8)src[lx->pos]) >= 0 || src[lx->pos] == '_')) {
          if (src[lx->pos] != '_') v = v * 16 + (u64)hexval((u8)src[lx->pos]);
          advance(lx, 1);
        }
      } else if (c == '0' && (c1 == 'b' || c1 == 'B')) {
        advance(lx, 2);
        while (lx->pos < len && (src[lx->pos] == '0' || src[lx->pos] == '1' || src[lx->pos] == '_')) {
          if (src[lx->pos] != '_') v = v * 2 + (u64)(src[lx->pos] - '0');
          advance(lx, 1);
        }
      } else {
        while (lx->pos < len && (is_digit((u8)src[lx->pos]) || src[lx->pos] == '_')) {
          if (src[lx->pos] != '_') {
            u64 d = (u64)(src[lx->pos] - '0');
            if (v > (~0ull - d) / 10) fatal_at(file, line, col, "integer literal does not fit in 64 bits");
            v = v * 10 + d;
          }
          advance(lx, 1);
        }
      }
      Token *t = push(lx, T_NUM, line, col, space);
      t->num = v;
      space = false;
      continue;
    }

    if (c == '"') {
      advance(lx, 1);
      Buf b = {0};
      while (lx->pos < len && src[lx->pos] != '"') {
        if (src[lx->pos] == '\\') {
          advance(lx, 1);
          if (src[lx->pos] == '\n') { // line continuation
            advance(lx, 1);
            while (src[lx->pos] == ' ' || src[lx->pos] == '\t') advance(lx, 1);
            continue;
          }
          put_utf8(&b, read_escape(lx));
        } else {
          buf_u8(&b, (u8)src[lx->pos]);
          advance(lx, 1);
        }
      }
      if (lx->pos >= len) fatal_at(file, line, col, "unterminated string");
      advance(lx, 1);
      Token *t = push(lx, T_STR, line, col, space);
      t->str = b.p ? b.p : "";
      t->slen = (int)b.len;
      space = false;
      continue;
    }

    if (c == '\'') {
      advance(lx, 1);
      u32 cp;
      if (src[lx->pos] == '\\') {
        advance(lx, 1);
        cp = read_escape(lx);
      } else {
        cp = read_codepoint(lx);
      }
      if (src[lx->pos] != '\'') fatal_at(file, line, col, "bad character literal");
      advance(lx, 1);
      Token *t = push(lx, T_CHAR, line, col, space);
      t->num = cp;
      space = false;
      continue;
    }

    // .ident and .number
    if (c == '.' && is_id_start(c1)) {
      advance(lx, 1);
      u64 start = lx->pos;
      for (;;) {
        while (lx->pos < len && is_id_char((u8)src[lx->pos])) advance(lx, 1);
        if (lx->pos < len && (src[lx->pos] == '!' || src[lx->pos] == '?') &&
            !(lx->pos + 1 < len && src[lx->pos + 1] == '='))
          advance(lx, 1);
        break; // one component per token: a.b.c postfix chains become several tokens
      }
      Token *t = push(lx, T_DOTID, line, col, space);
      t->text = intern_n(src + start, (int)(lx->pos - start));
      space = false;
      continue;
    }
    if (c == '.' && is_digit(c1) && !space) {
      advance(lx, 1);
      u64 v = 0;
      while (lx->pos < len && is_digit((u8)src[lx->pos])) {
        v = v * 10 + (u64)(src[lx->pos] - '0');
        advance(lx, 1);
      }
      Token *t = push(lx, T_DOTNUM, line, col, space);
      t->num = v;
      space = false;
      continue;
    }

    bool found = false;
    for (int i = 0; symbols[i]; i++) {
      u64 n = strlen(symbols[i]);
      if (lx->pos + n <= len && memcmp(src + lx->pos, symbols[i], n) == 0) {
        Token *t = push(lx, T_SYM, line, col, space);
        t->text = intern(symbols[i]);
        advance(lx, n);
        found = true;
        break;
      }
    }
    if (!found) fatal_at(file, line, col, "unexpected character (byte 0x%x)", (u32)c);
    space = false;
  }
  push(lx, T_EOF, lx->line, 0, true);
  TokenStream ts = {file, lx->toks, lx->ntoks};
  return ts;
}
