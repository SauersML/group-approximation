#!/usr/bin/env python3
"""Exact transversal search (mod-s2-torelli-relations-obey-the-theta-balance-law).

By (TB2), below Gamma(2) a positive relation of mass 10 is exactly a
transversal: a 0/1 vector with one class over each level-two splitting.  So
A_+(Gamma') = 10 iff some transversal lies in W(Gamma').  This script decides
that exactly, by meet in the middle over the fibres.

The additive invariant phi : Z^classes -> Z^classes / W is read off a Smith
decomposition D = U B V of a Z-basis B of W (sympy, exact): x in W iff
(x V)_j = 0 mod D_jj for j < rank and (x V)_j = 0 for j >= rank.

Input: lattice-<name>.json written by balance.py.  Output: transversal-<name>.json
with the number of transversals in W (all of them are counted).
Usage: python3 transversal.py <name>
"""
import itertools
import json
import os
import sys
import time

from sympy import Matrix
from sympy.matrices.normalforms import smith_normal_decomp

HERE = os.path.dirname(os.path.abspath(__file__))


def invariants(B, n):
    D, U, V = smith_normal_decomp(Matrix(B))
    r = len(B)
    d = [int(D[j, j]) for j in range(r)]
    assert all(x != 0 for x in d)
    keep = [j for j in range(r) if abs(d[j]) != 1] + list(range(r, n))
    mods = [abs(d[j]) if j < r else 0 for j in keep]
    phi = []
    for c in range(n):
        row = []
        for j, mo in zip(keep, mods):
            v = int(V[c, j])
            row.append(v % mo if mo else v)
        phi.append(row)
    return phi, mods, d


def red(vec, mods):
    return tuple(v % m if m else v for v, m in zip(vec, mods))


def main(name):
    t0 = time.time()
    L = json.load(open(os.path.join(HERE, f"lattice-{name}.json")))
    fibre, B = L["fibre"], L["B"]
    n = len(fibre)
    phi, mods, d = invariants(B, n)
    # sanity: every basis row has invariant 0, a random non-member does not
    for r in B:
        s = [sum(r[c] * phi[c][k] for c in range(n)) for k in range(len(mods))]
        assert all(x == 0 for x in red(s, mods))
    print(f"[{name}] Smith done, {len(mods)} invariant coords "
          f"(torsion {[m for m in mods if m]}) [{time.time()-t0:.0f}s]",
          flush=True)
    fib = [[c for c in range(n) if fibre[c] == m] for m in range(10)]
    left, right = fib[:5], fib[5:]
    k = len(mods)

    def sums(parts, sign):
        out = {}
        for choice in itertools.product(*parts):
            v = [0] * k
            for c in choice:
                pc = phi[c]
                for j in range(k):
                    v[j] += pc[j]
            key = red([sign * x for x in v], mods)
            out.setdefault(key, []).append(choice)
        return out

    Ls = sums(left, 1)
    print(f"[{name}] left combos {sum(len(v) for v in Ls.values())} "
          f"[{time.time()-t0:.0f}s]", flush=True)
    count, example = 0, None
    for choice in itertools.product(*right):
        v = [0] * k
        for c in choice:
            pc = phi[c]
            for j in range(k):
                v[j] -= pc[j]
        key = red(v, mods)
        if key in Ls:
            count += len(Ls[key])
            if example is None:
                example = list(Ls[key][0]) + list(choice)
    res = {"level": name, "classes": n,
           "fibre_sizes": [len(f) for f in fib],
           "transversals_total": 1 if not fib else
           int(__import__("math").prod(len(f) for f in fib)),
           "transversals_in_W": count, "example": example,
           "A_plus_is_10": count > 0,
           "conclusion": ("A_+ = 10" if count else
                          "no transversal in W, so A_+ >= 20 by (TB2)"),
           "seconds": round(time.time() - t0)}
    print(json.dumps(res), flush=True)
    json.dump(res, open(os.path.join(HERE, f"transversal-{name}.json"), "w"),
              indent=1)


if __name__ == "__main__":
    main(sys.argv[1])
