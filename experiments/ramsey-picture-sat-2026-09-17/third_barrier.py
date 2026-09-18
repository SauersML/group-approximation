"""Exact test of the 1/3 barrier of Thompson's F on the ball B_n, w.r.t. A = B_1.

w = alpha - beta with alpha = (1/3) x0^-1 + (2/3) x1 and beta = (1/3) x0 + (2/3) x1^-1
(the dual of the CEGAR witness at n = 7). The family Y_w = {P subset A : w(P) >= 1/3}.
SAT: is there E subset B_n with X_E(g) in Y_w for every g in I_n?
If yes, the model E is checked exactly (Fractions): every realized picture P has
w(P) >= 1/3, hence for every nu supported on I_n, sum_a w_a a nu(E) >= 1/3, hence
max_a a nu(E) - min_a a nu(E) >= 1/3 (as w = alpha - beta with alpha, beta probabilities),
so rho_F(B_1, n) >= 1/3 exactly.  If UNSAT, this particular w stops witnessing at radius n
(other w may still witness).
usage: python3 third_barrier.py {F|F2|Z2} nmin nmax
"""
import json
import sys
import time
from fractions import Fraction as Q

from pysat.solvers import Cadical153

from ramsey_sat import setup

# A order in groups.py: [e, x0, x0^-1, x1, x1^-1]
W = [Q(0), Q(-1, 3), Q(1, 3), Q(2, 3), Q(-2, 3)]
THR = Q(1, 3)


def wP(P):
    return sum(W[i] for i in range(5) if P >> i & 1)


FAM = [P for P in range(32) if wP(P) >= THR]


def test(name, n):
    t = time.time()
    dist, idx, interior, k = setup(name, n)
    forb = [P for P in range(32) if P not in FAM]
    s = Cadical153()
    for row in interior:
        for P in forb:
            s.add_clause([(-v if P >> i & 1 else v) for i, v in enumerate(row)])
    ok = s.solve()
    rec = {"group": name, "n": n, "ball": len(dist), "interior": len(interior),
           "family": FAM, "sat": ok}
    if ok:
        val = {abs(l): l > 0 for l in s.get_model()}
        Y = set()
        for row in interior:
            Y.add(sum(1 << i for i, v in enumerate(row) if val.get(v, False)))
        mn = min(wP(P) for P in Y)
        assert mn >= THR
        rec.update({"E_size": sum(1 for v in idx.values() if val.get(v, False)),
                    "realized": sorted(Y), "min_w_exact": str(mn)})
    s.delete()
    rec["seconds"] = round(time.time() - t, 1)
    return rec


if __name__ == "__main__":
    name, a, b = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    out = []
    for n in range(a, b + 1):
        r = test(name, n)
        print(json.dumps({k: v for k, v in r.items() if k != "family"}), flush=True)
        out.append(r)
        json.dump(out, open(f"third_barrier_{name}_n{a}-{b}.json", "w"), indent=1)
