/* Brute-force A_N for tiny words over {0,1}: enumerate ALL NFAs with Q states
 * (start 0, any final set), check unique acceptance of word w:
 *   - exactly one accepting path of length n, and
 *   - no other word of length n accepted.
 * (The first condition implies the second; we check path count == 1 and
 * that the word spelled... path count == 1 over ALL words is exactly:
 * sum over label-paths from 0 to F of length n == 1 AND w accepted.)
 * Usage: ./brute_an <word bits> <Q>
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main(int argc, char **argv) {
    const char *s = argv[1];
    int n = strlen(s), Q = atoi(argv[2]);
    int w[32];
    for (int i = 0; i < n; i++) w[i] = s[i] - '0';
    int nt = Q * 2 * Q; /* transition bits */
    if (nt > 25) { printf("too big\n"); return 1; }
    long long total = 1LL << nt;
    int bestfound = 0;
    for (long long mask = 0; mask < total; mask++) {
        /* adjacency: adj[a][p] = bitset of q */
        int adj[2][5];
        memset(adj, 0, sizeof adj);
        int bit = 0;
        for (int p = 0; p < Q; p++)
            for (int a = 0; a < 2; a++)
                for (int q = 0; q < Q; q++, bit++)
                    if (mask >> bit & 1) adj[a][p] |= 1 << q;
        /* accept w? forward subsets */
        int cur = 1;
        for (int i = 0; i < n && cur; i++) {
            int nx = 0;
            for (int p = 0; p < Q; p++) if (cur >> p & 1) nx |= adj[w[i]][p];
            cur = nx;
        }
        if (!cur) continue;
        /* total accepting paths of length n (all labels), capped */
        for (int F = 1; F < (1 << Q); F++) {
            if (!(cur & F)) continue;      /* w not accepted with this F */
            long long cnt[5];
            for (int q = 0; q < Q; q++) cnt[q] = (q == 0);
            for (int i = 0; i < n; i++) {
                long long nx[5] = {0};
                for (int p = 0; p < Q; p++) if (cnt[p])
                    for (int a = 0; a < 2; a++)
                        for (int q = 0; q < Q; q++)
                            if (adj[a][p] >> q & 1) {
                                nx[q] += cnt[p];
                                if (nx[q] > 3) nx[q] = 3;
                            }
                memcpy(cnt, nx, sizeof cnt);
            }
            long long tot = 0;
            for (int q = 0; q < Q; q++) if (F >> q & 1) tot += cnt[q];
            if (tot == 1) {
                printf("FOUND Q=%d mask=%lld F=%d\n", Q, mask, F);
                return 0;
            }
        }
    }
    printf("NONE with Q=%d\n", Q);
    return 0;
}
