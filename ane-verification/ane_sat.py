"""exact_nfa(word, Q): find a Q-state NFA exactly accepting `word`
(accepts it, and no other word of the same length over the word's alphabet),
or return None if none exists.  Start state 0.
"""
from pysat.solvers import Cadical153
from pysat.formula import IDPool

def exact_nfa(word, Q, alphabet=None, verbose=False):
    w = list(word)
    n = len(w)
    SIGMA = sorted(set(w)) if alphabet is None else sorted(alphabet)
    pool = IDPool()
    T = lambda p, a, q: pool.id(("T", p, a, q))
    Fv = lambda q: pool.id(("F", q))
    PI = lambda i, q: pool.id(("pi", i, q))
    P = lambda i, p, q, b: pool.id(("P", i, p, q, b))
    E = lambda p, q: pool.id(("E", p, q))
    cls = []
    cls.append([PI(0, 0)])
    for q in range(1, Q):
        cls.append([-PI(0, q)])
    for i in range(n + 1):
        cls.append([PI(i, q) for q in range(Q)])
        for q1 in range(Q):
            for q2 in range(q1 + 1, Q):
                cls.append([-PI(i, q1), -PI(i, q2)])
    for i in range(n):
        for p in range(Q):
            for q in range(Q):
                cls.append([-PI(i, p), -PI(i + 1, q), T(p, w[i], q)])
    for q in range(Q):
        cls.append([-PI(n, q), Fv(q)])
    for p in range(Q):
        for q in range(Q):
            for a in SIGMA:
                cls.append([-T(p, a, q), E(p, q)])
    cls.append([P(0, 0, 0, 0)])
    for i in range(n):
        for p in range(Q):
            for q in range(Q):
                pb0 = -P(i, p, q, 0)
                for a in SIGMA:
                    for p2 in range(Q):
                        ta = -T(p, a, p2)
                        for q2 in range(Q):
                            cls.append([pb0, ta, -T(q, a, q2), P(i+1, p2, q2, 0)])
                for a in SIGMA:
                    for a2 in SIGMA:
                        if a == a2: continue
                        for p2 in range(Q):
                            ta = -T(p, a, p2)
                            for q2 in range(Q):
                                cls.append([pb0, ta, -T(q, a2, q2), P(i+1, p2, q2, 1)])
                pb1 = -P(i, p, q, 1)
                for p2 in range(Q):
                    ep = -E(p, p2)
                    for q2 in range(Q):
                        cls.append([pb1, ep, -E(q, q2), P(i+1, p2, q2, 1)])
    for p in range(Q):
        for q in range(Q):
            cls.append([-P(n, p, q, 1), -Fv(p), -Fv(q)])
    if verbose:
        print(f"n={n} Q={Q} vars={pool.top} clauses={len(cls)}", flush=True)
    s = Cadical153(bootstrap_with=cls)
    if not s.solve():
        return None
    m = set(l for l in s.get_model() if l > 0)
    trans = [(p, a, q) for p in range(Q) for a in SIGMA for q in range(Q)
             if T(p, a, q) in m]
    fins = [q for q in range(Q) if Fv(q) in m]
    return {"Q": Q, "final": fins, "trans": trans}

if __name__ == "__main__":
    import sys, json
    word = sys.argv[1]
    Q = int(sys.argv[2])
    w = [int(c, 36) for c in word]
    r = exact_nfa(w, Q, verbose=True)
    print("SAT" if r else "UNSAT", flush=True)
    if r:
        from an_tools import check_exact, num_accepting_paths
        edges = set(map(tuple, r["trans"]))
        fins = set(r["final"])
        assert check_exact(edges, 0, fins, w)
        print("verified exact;",
              num_accepting_paths(edges, 0, fins, len(w)), "accepting paths")
        json.dump(r, open(f"nfa_{word}_Q{Q}.json", "w"))
