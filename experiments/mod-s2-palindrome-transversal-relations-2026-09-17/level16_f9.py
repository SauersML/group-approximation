#!/usr/bin/env python3
"""3-primary check of the level-16 Shapiro components over F_9 = F_3[i].

Same twisted Fox matrices as level16_betti.py (the 512-coset presentation of
K4 = M_4 twisted by C_f(I + 4X) = i^(f . Y), f in the dual of
A = Gamma(4)/Gamma(16) = Sym_4(Z/4)), reduced modulo the prime (3) of Z[i],
whose residue field is F_9 (3 is inert in Z[i]).

|A| = 4^10 is a unit in Z_(3), so Z_(3)[i][A] splits into characters and

    H_1(M_16; Z_(3)[i]) = (+)_f H_1(M_4; Z_(3)[i]_f).

For f != 0 the Fox cokernel is H_1(K4; Z_(3)[i]_f) (+) Z_(3)[i] (relative
class), so dim_F9 coker >= 1 + b_1^f + (number of 3-primary cyclic factors),
and dim_F9 coker = 1 certifies that H_1(M_4; Z_(3)[i]_f) = 0: b_1^f = 0 AND
no 3-torsion.  If this holds for every f != 0, then for every Gamma' with
Gamma(16) <= Gamma' <= Gamma(4) the kernel of
H_1(pi^-1 Gamma') -> H_1(M_4) is finite of order prime to 3.

    python3 level16_f9.py out.json
"""
import json
import os
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import level16_betti as L16  # noqa: E402

# F_9 = F_3[i], element a + b i encoded as a + 3 b
ADD = [[0] * 9 for _ in range(9)]
MUL = [[0] * 9 for _ in range(9)]
for x in range(9):
    for y in range(9):
        a, b = x % 3, x // 3
        c, d = y % 3, y // 3
        ADD[x][y] = (a + c) % 3 + 3 * ((b + d) % 3)
        MUL[x][y] = (a * c - b * d) % 3 + 3 * ((a * d + b * c) % 3)
NEG = [(-(x % 3)) % 3 + 3 * ((-(x // 3)) % 3) for x in range(9)]
INV = [0] * 9
for x in range(1, 9):
    INV[x] = [y for y in range(9) if MUL[x][y] == 1][0]
IPOW9 = np.array([1, 3, 2, 6], dtype=np.int64)       # 1, i, -1, -i


def rank_f9(row_id, gen, vals):
    R = {}
    for r, g, x in zip(row_id.tolist(), gen.tolist(), vals.tolist()):
        d = R.setdefault(r, {})
        nv = ADD[d.get(g, 0)][x]
        if nv:
            d[g] = nv
        else:
            d.pop(g, None)
    R = {r: d for r, d in R.items() if d}
    colrows = {}
    for r, d in R.items():
        for g in d:
            colrows.setdefault(g, set()).add(r)
    rank = 0
    while R:
        r = min(R, key=lambda r: len(R[r]))
        v = R.pop(r)
        for g in v:
            colrows[g].discard(r)
        j = min(v, key=lambda g: len(colrows.get(g, ())))
        inv = INV[v[j]]
        rank += 1
        for qq in list(colrows.get(j, ())):
            row = R[qq]
            f = NEG[MUL[row[j]][inv]]
            for g, b in v.items():
                nv = ADD[row.get(g, 0)][MUL[f][b]]
                if nv:
                    if g not in row:
                        colrows.setdefault(g, set()).add(qq)
                    row[g] = nv
                elif g in row:
                    del row[g]
                    colrows[g].discard(qq)
            if not row:
                del R[qq]
        colrows.pop(j, None)
    return rank


_T = {}


def component(args):
    k, f = args
    t0 = time.time()
    nrows, row_id, gen, sgn, P4 = _T["terms"]
    e = (P4 @ np.array(f, dtype=np.int64)) % 4
    vals = IPOW9[e]
    vals = np.where(sgn > 0, vals, np.array(NEG)[vals])
    rank = rank_f9(row_id, gen, vals)
    return k, {"coker_F9": len(L16.L.GEN) - rank,
               "seconds": round(time.time() - t0, 1)}


if __name__ == "__main__":
    out = sys.argv[1]
    t0 = time.time()
    orbits = L16.char_orbits()
    res = {"field": "F_9 = Z[i]/(3)", "orbits": orbits}
    _T["terms"] = L16.relator_terms(L16.schreier_images16())
    print("orbits", len(orbits), "relator rows", _T["terms"][0],
          f"[{time.time()-t0:.1f}s]", flush=True)
    import multiprocessing as mp
    nproc = int(os.environ.get("CHAR_PROCS", "1"))
    jobs = [(k, o["f"]) for k, o in enumerate(orbits)]
    with mp.get_context("fork").Pool(nproc) as pool:
        for k, c in pool.imap_unordered(component, jobs):
            orbits[k].update(c)
            o = orbits[k]
            o["h1_chi_F9_upper"] = c["coker_F9"] - (0 if o["order"] == 1
                                                   else 1)
            print(f"orbit {k} order {o['order']} size {o['size']}: "
                  f"coker_F9 {c['coker_F9']} [{c['seconds']}s]", flush=True)
            json.dump(res, open(out, "w"), indent=1)
    bad = [k for k, o in enumerate(orbits)
           if o["order"] > 1 and o["coker_F9"] != 1]
    res["nontrivial_orbits_with_coker_ne_1"] = bad
    res["kernel_prime_to_3_certified"] = not bad
    res["seconds"] = round(time.time() - t0, 1)
    print("orbits with coker_F9 != 1:", bad, flush=True)
    json.dump(res, open(out, "w"), indent=1)
    print("saved", out)
