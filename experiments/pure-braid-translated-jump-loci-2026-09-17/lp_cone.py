"""Push a Bestvina--Brady certificate onto a twist hyperplane by linear programming.

A certificate (a, eta) for fast_morse/climb3 is determined, as far as the ascending
posets Asc(C) go, by the lowest-vertex assignment low(k) of every cell k.  For that
assignment, the set of (a, eta) that realise it is an open polyhedral cone:
    (sep_k(D) - sep_k(low k)) . a + eta(D) - eta(low k) > 0   for every cell k, every D != low k.
Every (a, eta) in the cone gives the same Asc(C), hence the same (m-1)-connectivity.
This script keeps the assignment of a given certificate and asks the LP for a point of the
cone with the extra linear equations  sum a = 0  and  c_A(a) = 0  for the requested A
(0-indexed strand sets).  The strict inequalities become >= 1 (the cone is homogeneous).
A feasible point is rounded to integers (margin 1 is scaled to SCALE first) and written
as a certificate file that verify_cert.py re-checks from scratch.
Usage: python3 lp_cone.py cert.json 'A_json_list' out_tag [objective]
   A_json_list e.g. '[[0,1]]' or '[[0,1,2]]'.  objective: 'none' (default) or 'spread'
   ('spread' asks the other twist values c_B to stay at least 1 away from 0 on the side
   they have in the input certificate; this keeps the new character off the other twist
   hyperplanes)."""
import sys, json, itertools
import numpy as np
from scipy.optimize import linprog
from fast_morse import Salvetti, pairs

SCALE = 1000

def main():
    cert = json.load(open(sys.argv[1]))
    zeroA = [tuple(sorted(A)) for A in json.loads(sys.argv[2])]
    tag = sys.argv[3]
    objective = sys.argv[4] if len(sys.argv) > 4 else "none"
    n = cert["n"]; m = cert["m"]; K = cert["K"]
    S = Salvetti(n)
    P = S.P
    assert [tuple(c) for c in cert["chambers"]] == [tuple(c) for c in S.ch]
    a0 = np.array([float(x) * K for x in cert["a"]])
    eta0 = np.array(cert["eta"], dtype=float)
    npair, N = len(P), len(S.ch)
    rows = []
    for k, (ci, F) in enumerate(S.cells):
        st = S.stars[F]
        sep = (S.side[st] != S.side[ci]).astype(float)      # |st| x npair
        f = sep @ a0 + eta0[st]
        j = int(np.argmin(f))
        assert (f == f[j]).sum() == 1
        v = st[j]
        for t, D in enumerate(st):
            if D == v:
                continue
            r = np.zeros(npair + N)
            r[:npair] = sep[t] - sep[j]
            r[npair + D] += 1.0
            r[npair + v] -= 1.0
            rows.append(r)
    A_ub = -np.array(rows)            # -(row . x) <= -1
    b_ub = -np.ones(len(rows))
    eqs = [np.concatenate([np.ones(npair), np.zeros(N)])]
    for A in zeroA:
        e = np.zeros(npair + N)
        for p in itertools.combinations(A, 2):
            e[P.index(p)] = 1.0
        eqs.append(e)
    ub_extra, bub_extra = [], []
    if objective == "spread":
        for k in range(2, n):
            for B in itertools.combinations(range(n), k):
                if B in zeroA:
                    continue
                e = np.zeros(npair + N)
                for p in itertools.combinations(B, 2):
                    e[P.index(p)] = 1.0
                s0 = np.sign(e[:npair] @ a0)
                if s0 == 0:
                    continue
                ub_extra.append(-s0 * e); bub_extra.append(-1.0)
    if ub_extra:
        A_ub = np.vstack([A_ub, np.array(ub_extra)]); b_ub = np.concatenate([b_ub, bub_extra])
    # eta(ch[0]) = 0 pins the translation freedom of eta
    e0 = np.zeros(npair + N); e0[npair] = 1.0
    eqs.append(e0)
    A_eq = np.array(eqs); b_eq = np.zeros(len(eqs))
    print("constraints", A_ub.shape, "equations", A_eq.shape, flush=True)
    res = linprog(np.zeros(npair + N), A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq,
                  bounds=[(None, None)] * (npair + N), method="highs")
    print("status", res.status, res.message, flush=True)
    if res.status != 0:
        print("INFEASIBLE for this assignment")
        return
    x = res.x * SCALE
    a = np.rint(x[:npair]).astype(np.int64)
    for A in zeroA:           # restore exact equations after rounding
        idx = [P.index(p) for p in itertools.combinations(A, 2)]
        a[idx[-1]] -= a[idx].sum()
    # fix the total sum on a pair outside every zero set
    free = [i for i, p in enumerate(P) if not any(set(p) <= set(A) for A in zeroA)]
    a[free[-1]] -= a.sum()
    eta = np.rint(x[npair:]).astype(np.int64)
    out = {"n": n, "m": m, "a": [int(v) for v in a], "K": 1, "eta": [int(v) for v in eta],
           "chambers": [list(c) for c in S.ch], "from": sys.argv[1], "zero_sets": [list(A) for A in zeroA]}
    json.dump(out, open(f"cert_n{n}_m{m}_{tag}.json", "w"))
    print("a =", out["a"], "written", f"cert_n{n}_m{m}_{tag}.json", flush=True)

if __name__ == "__main__":
    main()
