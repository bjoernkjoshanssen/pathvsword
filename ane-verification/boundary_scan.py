"""Systematic scan of boundary configurations for the z_k lower bound.

For each surviving (l, d0) shape and each boundary schema, build the walk
graph and count accepting paths (cap 2).  A schema survives only if the
count is exactly 1.  We expect NO survivors anywhere.

Schemas (all with chain g_0..g_k distinct, c-edge -> h_0 = g_0, fold aligned
except where stated):

  S0  (u-pairings, b#=0): u1 = u2 = fresh?  s0=0 forbids fresh; the only
      pairing is u1 = u2 = one state (e-self-loop).
  S1a (b#=1, pairing (g_j*, 3k+6), (h_j*, n)): u1 = g_j*, u2 = h_j*-state=y.
  S1b (b#=1, pairing (g_j*, n), (h_j*, 3k+6)): u2 = g_j*, u1 = h_j*-state=y.
  S2a (b#=2, prefix-prefix + tail-tail + u-pair):
      g_{j1}=g_{j2}, h_{j1}=u1-state, h_{j2}=u2-state.
  S2b (b#=2, both tail states pair with u's, prefix states pair together):
      same as S2a up to relabeling; plus variant h_{j1}=h_{j2}, u1=g_{j1},
      u2=g_{j2}  (tail-tail double + two spanning chords).
Cluster shapes:
  l=1: loop at g_k + escape g_k->x1->x2->x3, c-edge from x3.
  l=2: entry g_k->P, cycle P<->Q, exit P->E1->E2, c-edge from E2.
  l=4: cycle {g_k=C0,C1,C2,C3}, run starts at C0 (= g_k, entry on cycle),
       exit at C_{m mod 4}, c-edge from there.
"""
import sys
sys.path.insert(0, '/home/claude')
from an_tools import num_accepting_paths


def zword(k):
    pref = []
    x = 0
    while len(pref) < k:
        if x not in (3, 4, 5, 6):
            pref.append(x)
        x += 1
    return pref + [3]*(k+5) + [4] + pref[:-1] + [5, 6], pref

D_LET, E_LET, C_LET, B_LET = 5, 6, 4, 3


def base_graph(k, l):
    """chain + cluster; returns (edges, exit_state, next_free_state_id)."""
    w, pref = zword(k)
    E = set()
    for i in range(k-1):
        E.add((i, pref[i], i+1))
    E.add((k-1, pref[k-1], k))       # into g_k
    nf = k+1
    m = k+5
    if l == 1:
        x1, x2, x3 = nf, nf+1, nf+2
        nf += 3
        E |= {(k, B_LET, k), (k, B_LET, x1), (x1, B_LET, x2), (x2, B_LET, x3)}
        exit_st = x3                  # T = [3, inf)
    elif l == 2:
        P, Q, E1, E2 = nf, nf+1, nf+2, nf+3
        nf += 4
        E |= {(k, B_LET, P), (P, B_LET, Q), (Q, B_LET, P),
              (P, B_LET, E1), (E1, B_LET, E2)}
        exit_st = E2                  # T = {3,5,7,...}
    elif l == 4:
        C1, C2, C3 = nf, nf+1, nf+2
        nf += 3
        E |= {(k, B_LET, C1), (C1, B_LET, C2), (C2, B_LET, C3),
              (C3, B_LET, k)}
        r = m % 4
        exit_st = [k, C1, C2, C3][r]  # T = {r + 4j}
    return E, exit_st, nf, pref


def tail_edges(E, pref, k, hs):
    """hs: list of tail states h_0..h_{k-1}; adds fold edges."""
    for i in range(k-1):
        E.add((hs[i], pref[i], hs[i+1]))


def scan(k, l):
    w, pref = zword(k)
    n = len(w)
    bad = []
    m = k + 5

    def check(E, final, tag):
        cnt = num_accepting_paths(E, 0, {final}, n)
        if cnt == 1:
            bad.append((tag, 'count=1'))

    # S0: u1 = u2 single state with e-self-loop
    E, ex, nf, pref_ = base_graph(k, l)
    hs = list(range(k))               # aligned: h_i = g_i
    E.add((ex, C_LET, hs[0]))
    tail_edges(E, pref, k, hs)
    u = nf
    E |= {(k-1, D_LET, u), (u, E_LET, u)}
    check(E, u, ('S0',))

    # S1a / S1b for each broken index j*
    for js in range(k-1):
        for variant in ('a', 'b'):
            E, ex, nf, _ = base_graph(k, l)
            y = nf                    # the broken tail state (double w/ a u-slot)
            hs = [(y if i == js else i) for i in range(k)]
            E.add((ex, C_LET, hs[0]))
            tail_edges(E, pref, k, hs)
            if variant == 'a':        # u1 = g_j*, u2 = y
                E |= {(k-1, D_LET, js), (js, E_LET, y)}
                check(E, y, ('S1a', js))
            else:                     # u1 = y, u2 = g_j*
                E |= {(k-1, D_LET, y), (y, E_LET, js)}
                check(E, js, ('S1b', js))

    # S2a: g_j1 = g_j2 (prefix-prefix), h_j1 = u1-state, h_j2 = u2-state
    for j1 in range(k-1):
        for j2 in range(j1+1, k-1):
            # prefix-prefix double: replace chain state j2 by j1
            E, ex, nf, _ = base_graph(k, l)
            E2 = set()
            ren = lambda s: j1 if s == j2 else s
            for (a, x, b) in E:
                E2.add((ren(a), x, ren(b)))
            y1, y2 = nf, nf+1
            hs = [(y1 if i == j1 else y2 if i == j2 else ren(i))
                  for i in range(k)]
            E2.add((ex, C_LET, hs[0]))
            for i in range(k-1):
                E2.add((hs[i], pref[i], hs[i+1]))
            E2 |= {(ren(k-1), D_LET, y1), (y1, E_LET, y2)}
            check(E2, y2, ('S2a', j1, j2))

    # S2b: h_j1 = h_j2 = y (tail-tail), u1 = g_j1, u2 = g_j2
    for j1 in range(k-1):
        for j2 in range(k-1):
            if j1 == j2:
                continue
            E, ex, nf, _ = base_graph(k, l)
            y = nf
            hs = [(y if i in (j1, j2) else i) for i in range(k)]
            E.add((ex, C_LET, hs[0]))
            tail_edges(E, pref, k, hs)
            E |= {(k-1, D_LET, j1), (j1, E_LET, j2)}
            check(E, j2, ('S2b', j1, j2))

    return bad


if __name__ == '__main__':
    for l, ks in [(1, [15, 18]), (2, [18, 24]), (4, [12, 24, 18, 30])]:
        for k in ks:
            m = k+5
            # shape validity: l=2 needs m odd (k even); l=4 needs m odd->d0 in {1,3}
            if l == 2 and m % 2 == 0:
                continue
            if l == 4 and m % 4 in (0, 2):
                continue
            bad = scan(k, l)
            print(f"l={l} k={k}: {'SURVIVORS: '+str(bad[:10]) if bad else 'all schemas die'}",
                  flush=True)
