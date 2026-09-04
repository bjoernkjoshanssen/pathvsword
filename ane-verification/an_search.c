/* Branch-and-bound: does word w admit a unique-acceptance walk with <= QMAX
 * states (QMAX <= 16)?  Walk = coloring c_0..c_n of positions; walk graph
 * must have exactly one path of length n from c_0 to c_n.
 * Canonical colorings: c_0 = 0, new color = (max so far)+1.
 * Usage: ./an_search <word digits> <QMAX>
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int n, QMAX;
static int w[64];
static int col[64];
static unsigned adj[36][32];   /* adj[a][p] = bitset of q */
static long long nodes = 0;
static int found = 0;

static int check(int upto) {
    int cnt[32], nxt[32];
    memset(cnt, 0, sizeof cnt);
    cnt[0] = 1;
    for (int t = 0; t < upto; t++) {
        memset(nxt, 0, sizeof nxt);
        for (int p = 0; p < QMAX; p++) {
            if (!cnt[p]) continue;
            for (int a = 0; a < 36; a++) {
                unsigned row = adj[a][p];
                while (row) {
                    int q = __builtin_ctz(row);
                    row &= row - 1;
                    nxt[q] += cnt[p];
                    if (nxt[q] > 2) nxt[q] = 2;
                }
            }
        }
        memcpy(cnt, nxt, sizeof cnt);
        if (cnt[col[t + 1]] >= 2) return 0;
    }
    return cnt[col[upto]] == 1;
}

static void rec(int i, int kmax) {
    if (found) return;
    nodes++;
    if (i == n) {
        printf("WITNESS with %d states: ", kmax);
        for (int t = 0; t <= n; t++) printf("%d ", col[t]);
        printf("\n");
        found = 1;
        return;
    }
    int a = w[i];
    int lim = kmax + 1; if (lim > QMAX) lim = QMAX;
    for (int nc = 0; nc < lim; nc++) {
        unsigned bit = 1u << nc;
        int added = !(adj[a][col[i]] & bit);
        adj[a][col[i]] |= bit;
        col[i + 1] = nc;
        if (check(i + 1))
            rec(i + 1, nc + 1 > kmax ? nc + 1 : kmax);
        if (added) adj[a][col[i]] &= ~bit;
        if (found) return;
    }
}

int main(int argc, char **argv) {
    const char *s = argv[1];
    n = strlen(s);
    for (int i = 0; i < n; i++)
        w[i] = (s[i] <= '9') ? s[i] - '0' : s[i] - 'a' + 10;
    QMAX = atoi(argv[2]);
    if (QMAX > 32) { printf("QMAX too big\n"); return 1; }
    col[0] = 0;
    rec(0, 1);
    if (!found) printf("UNSAT: no unique-acceptance walk with <= %d states (nodes=%lld)\n", QMAX, nodes);
    else printf("nodes=%lld\n", nodes);
    return 0;
}
