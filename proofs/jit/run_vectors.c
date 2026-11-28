/* Native x86-64 check of vectors.tsv (leansol ALU translation proof, runs/leansol-jitproof).
 * For every (code, input) pair: build prologue + listed bytes + two epilogues in an RWX page,
 * run it, and compare the 16 host registers (rsp/rbp checked against their entry values),
 * the frame word cpu[10], the temp word cpu[15] and the edge (fallthrough vs taken) with the
 * model's output row. Usage: run_vectors vectors.tsv  -> prints a summary, exit 1 on any mismatch. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <sys/mman.h>
#include <cpuid.h>

#define MAXIN 128
#define MAXCODE 1024
typedef struct { uint64_t g[16], frame, temp; } In;
typedef struct { int op, dst, src; char hex[256]; int site; } Code;
static In ins[MAXIN]; static int nin;
static Code codes[MAXCODE]; static int ncode;

static uint8_t *buf; static size_t n;
static void b(int x) { buf[n++] = (uint8_t)x; }
static void b32(uint32_t x) { for (int i = 0; i < 4; i++) b((x >> (8 * i)) & 0xff); }
static void b64(uint64_t x) { for (int i = 0; i < 8; i++) b((x >> (8 * i)) & 0xff); }

static void epilogue(uint32_t edge) {
  b(0x50);                                   /* push rax */
  b(0x48); b(0x8b); b(0x44); b(0x24); b(0x08); /* mov rax, [rsp+8]  (out pointer) */
  for (int i = 1; i < 16; i++) {             /* mov [rax+8*i], r_i */
    b(0x48 | ((i >> 3) << 2)); b(0x89); b(0x40 | ((i & 7) << 3)); b(8 * i);
  }
  b(0x59);                                   /* pop rcx  (guest-visible rax) */
  b(0x48); b(0x89); b(0x48); b(0x00);        /* mov [rax], rcx */
  b(0x48); b(0xc7); b(0x80); b32(128); b32(edge); /* mov qword [rax+128], edge */
  b(0x48); b(0x83); b(0xc4); b(0x08);        /* add rsp, 8 */
  b(0x41); b(0x5f); b(0x41); b(0x5e); b(0x41); b(0x5d); b(0x41); b(0x5c); /* pop r15..r12 */
  b(0x5d); b(0x5b); b(0xc3);                 /* pop rbp; pop rbx; ret */
}

static int hexval(char c) { return c <= '9' ? c - '0' : (c | 32) - 'a' + 10; }

int main(int argc, char **argv) {
  unsigned a, bx, c, d;
  int bmi2 = __get_cpuid_count(7, 0, &a, &bx, &c, &d) && (bx & (1u << 8));
  printf("cpu: bmi2=%d\n", bmi2);
  FILE *f = fopen(argc > 1 ? argv[1] : "vectors.tsv", "r");
  if (!f) { perror("vectors"); return 2; }
  static char line[4096];
  buf = mmap(0, 1 << 16, PROT_READ | PROT_WRITE | PROT_EXEC, MAP_PRIVATE | MAP_ANON, -1, 0);
  if (buf == MAP_FAILED) { perror("mmap"); return 2; }
  long pairs = 0, bad = 0, taken = 0;
  uint64_t cpu[32], out[17];
  fgets(line, sizeof line, f);               /* header */
  while (fgets(line, sizeof line, f)) {
    line[strcspn(line, "\n")] = 0;
    char *kind = strtok(line, "\t"), *id = strtok(0, "\t"), *data = strtok(0, "\t");
    if (!kind || !id || !data) continue;
    if (!strcmp(kind, "input")) {
      int k = atoi(id); uint64_t v[19]; char *p = data;
      for (int i = 0; i < 19; i++) { v[i] = strtoull(p, &p, 16); if (*p == ',') p++; }
      memcpy(ins[k].g, v, sizeof ins[k].g); ins[k].frame = v[16]; ins[k].temp = v[17];
      if (k + 1 > nin) nin = k + 1;
    } else if (!strcmp(kind, "code")) {
      Code *cd = &codes[atoi(id)]; char site[32] = "", imm[16];
      cd->hex[0] = 0;
      /* opcode,dst,src,imm32,hex,site ; hex may be empty */
      char *fld[6]; int nf = 0; char *p = data;
      fld[nf++] = p;
      for (; *p; p++) if (*p == ',') { *p = 0; fld[nf++] = p + 1; }
      if (nf != 6) { fprintf(stderr, "bad code row %s\n", id); return 2; }
      cd->op = (int)strtol(fld[0], 0, 16); cd->dst = atoi(fld[1]); cd->src = atoi(fld[2]);
      strncpy(imm, fld[3], 15); strncpy(cd->hex, fld[4], 255); strncpy(site, fld[5], 31);
      cd->site = strcmp(site, "-") ? atoi(site) : -1;
      if (atoi(id) + 1 > ncode) ncode = atoi(id) + 1;
    } else if (!strcmp(kind, "out")) {
      int ci = atoi(id), ii = atoi(strchr(id, '.') + 1);
      Code *cd = &codes[ci]; In *in = &ins[ii];
      /* expected = input + delta */
      uint64_t eg[16], ef = in->frame, et = in->temp; memcpy(eg, in->g, sizeof eg);
      char *p = data, *tok; int etaken = 0;
      char tmp[4096]; strncpy(tmp, p, sizeof tmp - 1); tmp[sizeof tmp - 1] = 0;
      for (tok = strtok(tmp, ","); tok; tok = strtok(0, ",")) {
        if (!strcmp(tok, "ok") || !strcmp(tok, "-")) continue;
        if (tok[0] == 'j') { etaken = 1; continue; }
        char *eq = strchr(tok, '='); uint64_t v = strtoull(eq + 1, 0, 16);
        if (tok[0] == 'r') eg[atoi(tok + 1)] = v; else if (tok[0] == 't') et = v; else if (tok[0] == 'f') ef = v;
      }
      /* build */
      n = 0;
      b(0x53); b(0x55); b(0x41); b(0x54); b(0x41); b(0x55); b(0x41); b(0x56); b(0x41); b(0x57); /* push rbx rbp r12-r15 */
      b(0x57);                                 /* push rdi (out) */
      b(0x48); b(0x89); b(0xa6); b32(8 * 20);  /* mov [rsi+160], rsp */
      b(0x48); b(0x89); b(0xf5);               /* mov rbp, rsi (cpu array) */
      for (int r = 0; r < 16; r++) {           /* movabs r, value (rsi/rdi last: they are free now) */
        if (r == 4 || r == 5) continue;
        b(0x48 | (r >> 3)); b(0xb8 | (r & 7)); b64(in->g[r]);
      }
      size_t start = n; size_t len = strlen(cd->hex) / 2;
      for (size_t i = 0; i < len; i++) b(hexval(cd->hex[2 * i]) * 16 + hexval(cd->hex[2 * i + 1]));
      epilogue(0);
      size_t second = n;
      epilogue(1);
      if (cd->site >= 0) {                     /* point the guarded branch at the second epilogue */
        size_t s = start + cd->site; int32_t rel = (int32_t)(second - (s + 4));
        memcpy(buf + s, &rel, 4);
      }
      memset(cpu, 0, sizeof cpu); cpu[10] = in->frame; cpu[15] = in->temp;
      memset(out, 0, sizeof out);
      ((void (*)(uint64_t *, uint64_t *))buf)(out, cpu);
      pairs++;
      int ok = 1;
      for (int r = 0; r < 16; r++) {
        uint64_t want = r == 5 ? (uint64_t)cpu : r == 4 ? cpu[20] - 8 : eg[r];
        if (out[r] != want) ok = 0;
      }
      if (cpu[10] != ef || cpu[15] != et || (int)out[16] != etaken) ok = 0;
      if (out[16]) taken++;
      if (!ok) {
        if (bad < 20) {
          printf("MISMATCH code %d input %d op=%02x d=%d s=%d bytes=%s:", ci, ii, cd->op, cd->dst, cd->src, cd->hex);
          for (int r = 0; r < 16; r++) if (r != 4 && r != 5 && out[r] != eg[r]) printf(" r%d=%016llx want %016llx", r, (unsigned long long)out[r], (unsigned long long)eg[r]);
          if (cpu[10] != ef) printf(" frame"); if (cpu[15] != et) printf(" temp=%llx want %llx", (unsigned long long)cpu[15], (unsigned long long)et);
          if ((int)out[16] != etaken) printf(" edge=%d want %d", (int)out[16], etaken);
          printf("\n");
        }
        bad++;
      }
    }
  }
  printf("recipes=%d inputs=%d pairs=%ld taken=%ld mismatches=%ld\n", ncode, nin, pairs, taken, bad);
  return bad ? 1 : 0;
}
