/* Exhaustive checker for sunflower3 v1 certificates (FORMAT.md), read from stdin.
 * For every block: members distinct, Sperner, 3-sunflower-free, all four port counts >= 1. Prints the port counts
 * and "OK <m>" per block, then "ALL BLOCKS OK"; on failure prints a witness and exits 1.
 * Sunflower test: for each member S, bucket the other members by A&S (hash table, O(m) per S); a 3-sunflower through
 * S exists iff some bucket holds two members whose parts outside S are disjoint. This covers every triple.
 * Build: cc -O2 -fopenmp check.c -o check      (without -fopenmp it runs single-threaded)
 * Use:   xz -dc CERT.txt.xz | ./check
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void die(const char *msg, long line) { printf("INVALID %s (line %ld)\n", msg, line); exit(1); }

static char *buf; static size_t blen, bpos; static long lineno;

/* next non-comment line, without its LF; NULL at end of input */
static char *next_line(void) {
    for (;;) {
        if (bpos >= blen) return NULL;
        char *s = buf + bpos, *e = memchr(s, '\n', blen - bpos);
        if (!e) die("missing final LF", lineno + 1);
        *e = 0; bpos = e - buf + 1; lineno++;
        if (s[0] != '#') return s;
    }
}

/* strict decimal token: 0 or [1-9][0-9]*; returns pointer after it, or NULL */
static const char *num(const char *s, long *v) {
    if (*s < '0' || *s > '9' || (*s == '0' && s[1] >= '0' && s[1] <= '9')) return NULL;
    long x = 0;
    while (*s >= '0' && *s <= '9') { x = x * 10 + (*s - '0'); if (x > 100000000L) return NULL; s++; }
    *v = x; return s;
}

static int cmpu(const void *a, const void *b) {
    uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b;
    int px = __builtin_popcountll(x), py = __builtin_popcountll(y);
    if (px != py) return px - py;
    return x < y ? -1 : x > y;
}

static inline uint64_t hsh(uint64_t k) { k ^= k >> 33; k *= 0xff51afd7ed558ccdULL; k ^= k >> 33; k *= 0xc4ceb9fe1a85ec53ULL; k ^= k >> 33; return k; }

static void check_block(uint64_t *F, long m) {
    qsort(F, m, 8, cmpu);
    for (long i = 1; i < m; i++) if (F[i] == F[i - 1]) { printf("DUPLICATE %llx\n", (unsigned long long)F[i]); exit(1); }
    long bad = -1, badj = -1;          /* a proper subset has smaller popcount: test i < j only */
    #pragma omp parallel for schedule(dynamic, 64)
    for (long i = 0; i < m; i++) {
        if (bad >= 0) continue;
        for (long j = i + 1; j < m; j++)
            if ((F[i] & ~F[j]) == 0) {
                #pragma omp critical
                { if (bad < 0) { bad = i; badj = j; } }
                break;
            }
    }
    if (bad >= 0) { printf("CONTAINMENT %llx %llx\n", (unsigned long long)F[bad], (unsigned long long)F[badj]); exit(1); }
    long cap = 1; while (cap < 2 * m) cap <<= 1;
    int found = 0; uint64_t w[3] = {0, 0, 0};
    #pragma omp parallel
    {
        long *head = malloc(sizeof(long) * cap), *next = malloc(sizeof(long) * m), *used = malloc(sizeof(long) * m);
        uint64_t *hkey = malloc(8 * cap);
        for (long t = 0; t < cap; t++) head[t] = -1;
        #pragma omp for schedule(dynamic, 16)
        for (long s = 0; s < m; s++) {
            int f;
            #pragma omp atomic read
            f = found;
            if (f) continue;
            uint64_t S = F[s]; long nu = 0;
            for (long j = 0; j < m; j++) {
                if (j == s) continue;
                uint64_t k = F[j] & S; long t = hsh(k) & (cap - 1);
                while (head[t] >= 0 && hkey[t] != k) t = (t + 1) & (cap - 1);
                if (head[t] < 0) { hkey[t] = k; used[nu++] = t; next[j] = -1; } else next[j] = head[t];
                head[t] = j;
            }
            for (long u = 0; u < nu; u++)
                for (long x = head[used[u]]; x >= 0; x = next[x]) {
                    uint64_t ox = F[x] & ~S;
                    for (long y = next[x]; y >= 0; y = next[y])
                        if ((ox & F[y]) == 0) {   /* F[x], F[y] agree on S, so this is (F[x]&~S) & (F[y]&~S) == 0 */
                            #pragma omp critical
                            { if (!found) { found = 1; w[0] = S; w[1] = F[x]; w[2] = F[y]; } }
                            goto done;
                        }
                }
        done:
            for (long u = 0; u < nu; u++) head[used[u]] = -1;
        }
        free(head); free(hkey); free(next); free(used);
    }
    if (found) { printf("SUNFLOWER %llx %llx %llx\n", (unsigned long long)w[0], (unsigned long long)w[1], (unsigned long long)w[2]); exit(1); }
}

int main(void) {
    size_t cap = 1 << 20; buf = malloc(cap);
    size_t r;
    while ((r = fread(buf + blen, 1, cap - blen, stdin)) > 0) { blen += r; if (blen == cap) buf = realloc(buf, cap *= 2); }
    if (memchr(buf, '\r', blen)) die("CR character", 0);
    char *l = next_line();
    if (!l || strcmp(l, "sunflower3 v1")) die("header", lineno);
    int nblocks = 0;
    while ((l = next_line()) != NULL) {
        if (l[0] == 0 && bpos >= blen) break;                 /* tolerate one empty last line */
        long n, p, q, m; const char *s = l;
        if (strncmp(s, "block ", 6)) die("expected block line", lineno);
        s += 6;
        if (!(s = num(s, &n)) || *s++ != ' ' || !(s = num(s, &p)) || *s++ != ' ' || !(s = num(s, &q)) || *s++ != ' ' ||
            !(s = num(s, &m)) || *s) die("bad block line", lineno);
        if (n < 3 || n > 64 || p >= n || q >= n || p == q || m < 1) die("bad block header", lineno);
        uint64_t *F = malloc(8 * m);
        for (long i = 0; i < m; i++) {
            if (!(l = next_line())) die("too few members", lineno);
            uint64_t D = 0; long prev = -1, v;
            if (strcmp(l, "-")) {
                s = l;
                for (;;) {
                    if (!(s = num(s, &v)) || v <= prev || v >= n) die("bad member line", lineno);
                    D |= 1ULL << v; prev = v;
                    if (*s == 0) break;
                    if (*s++ != ' ') die("bad member line", lineno);
                }
            }
            F[i] = D;
        }
        long N[2][2] = {{0, 0}, {0, 0}};
        for (long i = 0; i < m; i++) N[(F[i] >> p) & 1][(F[i] >> q) & 1]++;
        printf("block %d: n=%ld p=%ld q=%ld m=%ld  N00=%ld N01=%ld N10=%ld N11=%ld\n", ++nblocks, n, p, q, m,
               N[0][0], N[0][1], N[1][0], N[1][1]);
        if (!N[0][0] || !N[0][1] || !N[1][0] || !N[1][1]) die("a port count is zero", lineno);
        fflush(stdout);
        check_block(F, m);
        printf("OK %ld\n", m); fflush(stdout);
        free(F);
    }
    if (!nblocks) die("no block", lineno);
    printf("ALL BLOCKS OK\n");
    return 0;
}
