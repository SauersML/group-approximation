#!/usr/bin/env python3
"""Independent homomorphism-count check of the 2x4 and 3x4 census.

For every table T and each finite group F in the list:
  obs  = |Hom(P(T), F)| counted over ALL generator tuples of the ORIGINAL presentation
         (vectorized: for each assignment, a table is satisfied iff the products
         x_s x_m agree on every block; no Tietze move is used);
  fin  = |F|^(free generators) * prod |Hom(C, F)| over the components C of the FINAL
         presentation produced by the pipeline (simplify, then certify_component for
         the components that recognize() leaves open), counted by brute force;
  name = prod of |Hom(G_i, F)| over the claimed factor NAMES, for the names whose
         count is determined by the name (every name except finite(N) and Z/n:Z,
         which are checked at the component level only).
A mismatch between obs and fin refutes a Tietze step; between fin and name, a
recognition step.
"""
import itertools
import sys

import numpy as np

from classify import components, recognize
from homcheck import get_group, factor_count, presentation_count
from recognize_ext import certify_component
from tables import tables_fast, gen_names
from tietze import simplify


def name_count(name, G):
    N, mul, inv = G
    if name.startswith("finite(") or ":Z" in name:
        return None
    if name.startswith("T("):
        p, q = (int(t) for t in name[2:-1].split(","))
        return sum(1 for a, b in itertools.product(range(N), repeat=2)
                   if power(a, p, mul) == power(b, q, mul))
    if name.startswith("BS(1,"):
        n = int(name[5:-1])
        # <a,t | t a t^-1 = a^n>
        cnt = 0
        for a, t in itertools.product(range(N), repeat=2):
            lhs = mul[mul[t][a]][inv[t]]
            rhs = power(a, n, mul) if n >= 0 else inv[power(a, -n, mul)]
            cnt += (lhs == rhs)
        return cnt
    if name == "Z/3xZ":
        return sum(1 for a, b in itertools.product(range(N), repeat=2)
                   if mul[a][b] == mul[b][a] and power(a, 3, mul) == 0)
    return factor_count(name, G)


def power(a, k, mul):
    y = 0
    for _ in range(k):
        y = mul[y][a]
    return y


def main(group_names, shapes):
    mismatches = 0
    checked = named = 0
    for gname in group_names:
        G = get_group(gname)
        N, mul, inv = G
        M = np.array(mul, dtype=np.int16)
        cache = {}
        comp_count = {}
        for shape in shapes:
            ns, nm = shape
            ng = len(gen_names(ns, nm))
            A = np.array(list(itertools.product(range(N), repeat=ng)), dtype=np.int16)
            # x_1 = identity; generator order s1..s_(ns-1), m1..m_(nm-1)
            xs = [np.zeros(len(A), dtype=np.int16)] + [A[:, i] for i in range(ns - 1)]
            xm = [np.zeros(len(A), dtype=np.int16)] + [A[:, ns - 1 + j] for j in range(nm - 1)]
            P = {(s, m): M[xs[s], xm[m]] for s in range(ns) for m in range(nm)}
            for tid, (part, rels) in enumerate(tables_fast(ns, nm)):
                ok = np.ones(len(A), dtype=bool)
                for b in part:
                    for c in b[1:]:
                        ok &= (P[b[0]] == P[c])
                obs = int(ok.sum())
                gens = list(range(1, ng + 1))
                g2, r2 = simplify(gens, rels)
                fin, pred, have_name = 1, 1, True
                for cg, crels in components(g2, r2):
                    k = recognize(cg, crels)
                    if k is not None:
                        finals, names = [(cg, crels)], [k]
                    else:
                        key = (tuple(sorted(cg)), tuple(sorted(crels)))
                        if key not in cache:
                            res = certify_component(cg, crels)
                            assert res[0] is not None, (shape, tid, key)
                            cache[key] = (res[2], res[0])
                        finals, names = cache[key]
                    for fg, frels in finals:
                        fkey = (tuple(sorted(fg)), tuple(sorted(frels)))
                        if fkey not in comp_count:
                            idx = {g: n + 1 for n, g in enumerate(sorted(fg))}
                            rr = [tuple(idx[abs(x)] * (1 if x > 0 else -1) for x in r)
                                  for r in frels]
                            comp_count[fkey] = presentation_count(len(fg), rr, G)
                        fin *= comp_count[fkey]
                    for nm_ in names:
                        c = name_count(nm_, G)
                        if c is None:
                            have_name = False
                        else:
                            pred *= c
                checked += 1
                if obs != fin or (have_name and pred != fin):
                    mismatches += 1
                    print("MISMATCH", gname, shape, tid, obs, fin, pred if have_name else None)
                named += have_name
            print(gname, shape, "done", flush=True)
    print(f"checked {checked} (table, group) pairs over {group_names} and shapes {shapes}; "
          f"name-level count available for {named}; {mismatches} mismatches")


if __name__ == "__main__":
    groups = sys.argv[1].split(",")
    shapes = [tuple(int(t) for t in s.split("x")) for s in sys.argv[2].split(",")]
    main(groups, shapes)
