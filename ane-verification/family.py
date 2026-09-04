"""The family w^(C), C >= 4, k = C-1:
   w = l_1 ... l_k  3^(k+5)  4  l_1 ... l_{k-1}  5 6
Letters: l_1..l_{k-1} occur twice; l_k, 4, 5, 6 once; 3 occurs m=k+5 times.
|w| = 3k+7 = 3C+4.

Claimed exact acceptor with C+4 = k+5 states:
  chain s_0 -l_1-> s_1 -l_2-> ... -l_{k-1}-> s_{k-1};
  s_{k-1} -l_k-> A;  gadget on letter 3: A->X, X->B, B->A, B->B;
  X -4-> s_0;  s_{k-1} -5-> t1 -6-> t2 (final).
Run-length set T(A->X) = {1} u [4,oo).
"""
from an_tools import check_exact, num_accepting_paths

def family_word(C):
    k = C - 1
    # letters: use integers; prefix letters: 0,1,2,7,8,9,10,11,... avoiding 3,4,5,6
    pref = []
    x = 0
    while len(pref) < k:
        if x not in (3, 4, 5, 6):
            pref.append(x)
        x += 1
    w = pref + [3] * (k + 5) + [4] + pref[:-1] + [5, 6]
    return w, pref

def family_nfa(C):
    k = C - 1
    w, pref = family_word(C)
    # states: 0..k-1 chain, A=k, X=k+1, B=k+2, t1=k+3, t2=k+4
    A, X, B, t1, t2 = k, k + 1, k + 2, k + 3, k + 4
    edges = set()
    for i in range(k - 1):
        edges.add((i, pref[i], i + 1))
    edges.add((k - 1, pref[k - 1], A))
    edges |= {(A, 3, X), (X, 3, B), (B, 3, A), (B, 3, B)}
    edges.add((X, 4, 0))
    edges |= {(k - 1, 5, t1), (t1, 6, t2)}
    return edges, 0, {t2}, k + 5

if __name__ == "__main__":
    for C in range(4, 12):
        w, pref = family_word(C)
        edges, q0, fins, nstates = family_nfa(C)
        ok = check_exact(edges, q0, fins, w)
        np_ = num_accepting_paths(edges, q0, fins, len(w))
        print(f"C={C} |w|={len(w)} states={nstates} exact={ok} paths={np_}")
