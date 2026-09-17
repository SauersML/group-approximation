"""Turn-graph obstruction census for legal f-folded certificates on the rose (positive automorphisms of F_3).

For a positive train-track automorphism f = phi^m of F_3 on the rose, a legal f-folded
fatgraph X (conditions (2),(3),(4) of Calegari--Walker) has chi(X) < 0 only if some vertex
has valence >= 4.  Such a vertex is not an f-vertex (those are bivalent), carries at most one
d^- corner (condition (4)), and all its other corners are turns inside blocks f(x).  By the
sign-parity lemma its directions alternate in sign and lie in distinct gates.  Hence the
Whitehead graph T_m of turns taken inside the words f(x) = phi^m(x) contains a path
p1 - N1 - p2 - N2 with p1, p2 positive directions in distinct gates and N1, N2 negative
directions in distinct gates.  Since T_m is contained in T_inf (turns of all phi^k(x)), and
gates do not depend on m, absence of such a path in T_inf, or min(#positive gates,
#negative gates) <= 1, kills certificates for every power m, every boundary and every cover.

usage: python3 turn_graph_obstruction.py phi_scan4.json
Prints census counts and examples.
"""
import sys, json
from collections import Counter
from ffold import inv, apply, gate_of

def turn_closure(phi, K=8, cap=4000):
    T = set()
    for x in "abc":
        w = x
        for _ in range(K):
            w = apply(phi, w)
            if len(w) > cap: w = w[:cap]
            for i in range(len(w) - 1):
                T.add(frozenset((inv(w[i]), w[i + 1])))
    return T

def has_path(phi, g, T):
    adj = {d: set() for d in "abcABC"}
    for t in T:
        u, v = tuple(t) if len(t) == 2 else (next(iter(t)),) * 2
        adj[u].add(v); adj[v].add(u)
    for p1 in "abc":
        for N1 in adj[p1]:
            if N1.islower(): continue
            for p2 in adj[N1]:
                if not p2.islower() or g[p2] == g[p1]: continue
                for N2 in adj[p2]:
                    if N2.isupper() and g[N2] != g[N1]:
                        return (p1, N1, p2, N2)
    return None

def classify(phi):
    g = gate_of(phi)
    gp = len({g[d] for d in "abc"}); gn = len({g[d] for d in "ABC"})
    if min(gp, gn) <= 1:
        return "killed: min gates <= 1", None
    path = has_path(phi, g, turn_closure(phi))
    if path is None:
        return "killed: no alternating legal 3-path in taken-turn graph", None
    return "survives", path

if __name__ == "__main__":
    data = json.load(open(sys.argv[1]))
    C = Counter(); ex = {}
    for r in data:
        phi = r[2]
        c, path = classify(phi)
        C[c] += 1
        ex.setdefault(c, (phi, r[4], path))
    print("automorphisms in census:", len(data))
    for c, n in sorted(C.items()):
        print(n, c, "example:", ex[c])
