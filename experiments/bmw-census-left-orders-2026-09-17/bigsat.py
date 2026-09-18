# Larger positive-cone SAT instances for single classes (same CNF as lo_census.lo_sat, streamed into the
# solver so that the clause list is never held in Python).  Run once per solver; both must agree.
# usage: bigsat.py census.json idx R short
import sys, json, time
from pysat.solvers import Cadical153, Glucose4
from lo_census import load, ball

def clauses(G, R, short):
    idx, els = ball(G, R)
    K = [i for i, (v, h) in enumerate(els) if i > 0 and len(v) % 2 == 0 and len(h) % 2 == 0]
    for i in K:
        g = els[i]
        gi = G.mul(((), tuple(G.iA[x] for x in reversed(g[1]))), (tuple(G.iB[x] for x in reversed(g[0])), ()))
        j = idx[gi]; assert j != i and G.mul(g, gi) == ((), ())
        if i < j: yield [i, j]; yield [-i, -j]
    left = [i for i in K if len(els[i][0]) + len(els[i][1]) <= short]
    lset = set(left)
    for a in left:
        ea = els[a]
        for b in K:
            eb = els[b]
            k = idx.get(G.mul(ea, eb))              # pair (a, b)
            if k is not None: yield [-a, -b] if k == 0 else [-a, -b, k]
            if b in lset and b <= a: continue       # pair (b, a) already produced as (a', b') with a' = b
            k = idx.get(G.mul(eb, ea))              # pair (b, a)
            if k is not None: yield [-b, -a] if k == 0 else [-b, -a, k]

if __name__ == "__main__":
    path, want, R, short = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    G = next(G for i, G in load(path) if i == want)
    res = []
    for S in (Cadical153, Glucose4):
        t = time.time(); n = 0
        with S() as sv:
            for c in clauses(G, R, short):
                sv.add_clause(c); n += 1
            r = sv.solve()
        res.append(r)
        print(json.dumps(dict(census=path, idx=want, R=R, short=short, solver=S.__name__, sat=r, clauses=n,
                              secs=round(time.time() - t, 1))), flush=True)
    assert len(set(res)) == 1
