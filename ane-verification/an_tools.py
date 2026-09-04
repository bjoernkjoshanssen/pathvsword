"""Tools for automatic complexity experiments.

A_N(x): min states of an NFA uniquely accepting x (exact + one accepting path).
Fact (trim argument): WLOG the NFA's states/transitions all lie on the unique
accepting path and the final state is the path's endpoint.  So a witness is a
coloring c_0..c_n of positions by states such that the walk graph
E = {(c_i, x_i, c_{i+1})} has exactly ONE path of length n from c_0 to c_n.

Enumerate colorings as restricted growth strings (canonical set partitions),
with sound pruning: if the partial walk graph already has >=2 paths of length
t from c_0 to c_t, the full count will be >=2 (append the walk's suffix).
"""
from functools import lru_cache

def count_paths(edges, start, end, n, cap=2):
    """# length-n paths start->end in labeled digraph, counts capped at cap."""
    cur = {start: 1}
    for _ in range(n):
        nxt = {}
        for p, c in cur.items():
            for (pp, a, q) in edges:
                if pp == p:
                    nxt[q] = min(cap, nxt.get(q, 0) + c)
        cur = nxt
    return cur.get(end, 0)

def AN(x, maxq=None):
    n = len(x)
    if n == 0:
        return 1
    if maxq is None:
        maxq = n // 2 + 1
    best = [None]

    def rec(i, colors, kmax, edges, cnts):
        # colors: c_0..c_i assigned; kmax = #colors used; cnts: path counts to
        # each state at time i (capped at 2).
        if best[0] is not None and kmax >= best[0]:
            return
        if i == n:
            if cnts.get(colors[-1], 0) == 1:
                best[0] = kmax
            return
        a = x[i]
        for nc in range(min(kmax + 1, maxq)):  # restricted growth
            e = (colors[i], a, nc)
            if e in edges:
                edges2 = edges
                added = False
            else:
                edges2 = edges | {e}
                added = True
            # recompute path counts at time i+1 from scratch is costly;
            # incremental: with a possibly-new edge, counts at earlier times
            # can change! (new edge may create earlier paths). So recompute.
            cur = {colors[0]: 1}
            ok = True
            for t in range(i + 1):
                nxt = {}
                for p, c in cur.items():
                    for (pp, aa, q) in edges2:
                        if pp == p:
                            nxt[q] = min(2, nxt.get(q, 0) + c)
                cur = nxt
                # prune: >=2 paths (any labels) arriving at the walk state
                # at time t+1 -- the walk's suffix extends each to a full
                # accepting path, so uniqueness is already dead.
                if t + 1 <= i and cur.get(colors[t + 1], 0) >= 2:
                    ok = False; break
            if ok and cur.get(nc, 0) >= 2:
                ok = False
            if ok:
                rec(i + 1, colors + [nc], max(kmax, nc + 1), edges2, cur)

    rec(0, [0], 1, frozenset(), {0: 1})
    return best[0]

def exact_word_count(edges, start, finals, n, alphabet, cap=2):
    """# distinct words of length n accepted (subset construction), capped."""
    from itertools import product
    start_set = frozenset([start])
    memo = {}
    def go(t, S):
        if t == n:
            return 1 if S & finals else 0
        key = (t, S)
        if key in memo:
            return memo[key]
        tot = 0
        for a in alphabet:
            T = frozenset(q for (p, aa, q) in edges if aa == a and p in S)
            if T:
                tot += go(t + 1, T)
                if tot >= cap:
                    tot = cap; break
        memo[key] = tot
        return tot
    return go(0, start_set)

def num_accepting_paths(edges, start, finals, n):
    cur = {start: 1}
    for _ in range(n):
        nxt = {}
        for p, c in cur.items():
            for (pp, a, q) in edges:
                if pp == p:
                    nxt[q] = nxt.get(q, 0) + c
        cur = nxt
    return sum(c for q, c in cur.items() if q in finals)

def check_exact(edges, start, finals, x, alphabet=None):
    """True iff NFA accepts x and no other word of len |x| (over alphabet)."""
    n = len(x)
    if alphabet is None:
        alphabet = sorted(set(a for (_, a, _) in edges))
    # accepts x?
    cur = {start}
    for a in x:
        cur = {q for (p, aa, q) in edges if aa == a and p in cur}
    if not (cur & finals):
        return False
    return exact_word_count(edges, start, finals, n, alphabet) == 1

if __name__ == "__main__":
    # sanity checks
    assert AN((0,)) == 1
    assert AN((0, 1)) == 2
    assert AN((0, 1, 1)) == 2  # Hyde bound floor(3/2)+1 = 2, achieved
    assert AN((0, 1, 2)) == 2
    assert AN((0,)*6) == 1
    print("sanity ok")
    print("AN(0110)=", AN((0,1,1,0)))
    print("AN(010101)=", AN((0,1,0,1,0,1)))
