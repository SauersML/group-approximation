"""Decide whether the ball B_n is 1/2-Ramsey with respect to B_1 (Moore's definition).

B_n is NOT 1/2-Ramsey w.r.t. A iff some E subset of B_n has a non-(1/2)-balanced picture
collection {X_E(g) : g in I_n}, where I_n = {g : A g subset of B_n} and
X_E(g) = {a in A : a g in E} (Moore, Prop. 5.1 and its converse; see the research node).
Equivalently: for one of the inclusion-maximal non-balanced families Y (families.py),
the CNF "X_E(g) in Y for every g in I_n" is satisfiable.

usage: python3 ramsey_sat.py {F|F2} n_max
"""
import json
import sys
import time

from pysat.solvers import Cadical153

import groups


def setup(name, n):
    """Cached (pickle in the scratch dir given by env RAMSEY_CACHE, if set)."""
    import os
    import pickle
    cdir = os.environ.get("RAMSEY_CACHE")
    if cdir:
        path = os.path.join(cdir, f"setup_{name}_{n}.pkl")
        if os.path.exists(path):
            return pickle.load(open(path, "rb"))
        out = _setup(name, n)
        pickle.dump(out, open(path, "wb"))
        return out
    return _setup(name, n)


def _setup(name, n):
    if name == "F":
        gens, ident, mul, A = groups.F_GENS, groups.F_ID, groups.f_mul, groups.F_A1
    elif name == "Z2":
        gens, ident, mul, A = groups.Z_GENS, groups.Z_ID, groups.z_mul, groups.Z_A1
    else:
        gens, ident, mul, A = groups.W_GENS, groups.W_ID, groups.w_mul, groups.W_A1
    dist = groups.ball(gens, ident, mul, n)
    idx = {g: i + 1 for i, g in enumerate(dist)}  # SAT variables 1..|B_n|
    interior = []
    for g in dist:
        row = []
        for a in A:
            h = mul(a, g)
            if h not in idx:
                break
            row.append(idx[h])
        else:
            interior.append(row)
    return dist, idx, interior, len(A)


def realizable(interior, k, fam, solver_cls=Cadical153):
    allowed = set(fam)
    forb = [Q for Q in range(1 << k) if Q not in allowed]
    s = solver_cls()
    for row in interior:
        for Q in forb:
            s.add_clause([(-v if Q >> i & 1 else v) for i, v in enumerate(row)])
    ok = s.solve()
    model = s.get_model() if ok else None
    s.delete()
    return ok, model


if __name__ == "__main__":
    name, nmax = sys.argv[1], int(sys.argv[2])
    ffile = sys.argv[3] if len(sys.argv) > 3 else "families_k5.json"
    nmin = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    fams = json.load(open(ffile))["maximal"]
    tag = "closed" if "closed" in ffile else "open"
    results = []
    for n in range(nmin, nmax + 1):
        t = time.time()
        dist, idx, interior, k = setup(name, n)
        sat = []
        for j, fam in enumerate(fams):
            ok, _ = realizable(interior, k, fam)
            if ok:
                sat.append(j)
        rec = {"group": name, "families": tag, "n": n, "ball": len(dist),
               "interior": len(interior),
               "realizable_families": sat, "ramsey": len(sat) == 0,
               "seconds": round(time.time() - t, 1)}
        print(json.dumps(rec), flush=True)
        results.append(rec)
        if not sat:
            break
    json.dump(results, open(f"ramsey_B1_{name}_{tag}_n{nmin}-{nmax}.json", "w"), indent=1)
