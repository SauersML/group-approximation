#!/usr/bin/env python3
"""Exact edge-isoperimetric certificates for the Cayley graph of Thompson's group F
with the standard generators S = {x0^{+-1}, x1^{+-1}}.

Gamma = Cay(F, S) is 4-regular, simple (the four generators are distinct) and
bipartite (F abelianizes to Z^2, so every closed walk has even length).  For a
finite vertex set A put

    b(A) = |partial A| / |A|,   |partial A| = 4|A| - 2 e(A),

with e(A) the number of edges of Gamma inside A.

DIRECTION WARNING (corrected 2026-09-18; the earlier text here was false and was
falsely attributed to the route node, which proves the opposite).  The
Kesten--Dodziuk inequality reads

    sup spec P <= sqrt(1 - (h/4)^2),   equivalently   h <= 4 sqrt(1 - ||P||^2),

for P = (x0 + x0^-1 + x1 + x1^-1)/4 on l^2(F) and h = h(F, S) the Cheeger
constant.  It converts a LOWER bound on h into an UPPER bound on ||P||.  A single
explicit finite set A gives only an UPPER bound h <= b(A), which is the wrong
side on both counts, so NOTHING about ||P|| follows from it through
Kesten--Dodziuk.  What does survive from an explicit A is the elementary
Rayleigh quotient of the indicator vector 1_A,

    ||P|| >= <P 1_A, 1_A> / <1_A, 1_A> = 1 - b(A)/4,

which for the best set found below (b = 1.40743) is only ||P|| >= 0.6481, and
which is in any case dominated by lambda_max(A_A)/4 from ball_eigen.py.  So this
script computes an exact upper bound on h and a weak lower bound on ||P||; it is
recorded as a dead end, not as a competitive certificate.  Everything below is
integer arithmetic: |A| and e(A) are counted exactly.

Method.  Build the ball B_R of Gamma exactly (tree-pair normal forms, canonical
integer keys, see f_elements.py).  Every vertex of B_{R-1} has all four of its
neighbours inside B_R, so for any A inside B_{R-1} the induced subgraph H on
B_{R-1} records every edge of Gamma inside A, and e(A) = e_H(A) exactly.
Minimising b over subsets of B_{R-1} is exactly the maximum-density subgraph
problem for H.  We run Charikar's min-degree peeling and then the exact local
search (remove every vertex of inner degree below the current density, add every
outside vertex of inner degree above it), which increases the density
monotonically.  Any set the search returns is a valid certificate; only its
optimality is heuristic.

Usage:  python3 ball_boundary.py R [--out out.json] [--dump keys.txt]
"""
import argparse
import array
import json
import os
import sys
import time

sys.setrecursionlimit(10000)
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from f_elements import TIDENT, TGENS, key, unkey, tmul  # noqa: E402


def build_ball(R, log=lambda s: None):
    """Vertices of B_R with BFS levels, plus neighbour indices (-1 outside B_R)."""
    t0 = time.time()
    idx = {key(TIDENT): 0}
    keys = [key(TIDENT)]
    level = array.array("b", [0])
    frontier = [0]
    for r in range(1, R + 1):
        nxt = []
        for i in frontier:
            g = unkey(keys[i])
            for s in TGENS:
                k = key(tmul(g, s))
                if k not in idx:
                    idx[k] = len(keys)
                    keys.append(k)
                    level.append(r)
                    nxt.append(len(keys) - 1)
        frontier = nxt
        log(f"  r={r}: sphere {len(nxt)} ball {len(keys)} ({time.time()-t0:.1f}s)")
    return keys, idx, level


def adjacency(keys, idx, level, R):
    """4 neighbour indices per vertex of B_{R-1}; entries pointing into the outer
    sphere are recorded as -1 (they are edges leaving B_{R-1} and count towards the
    boundary, but never join two vertices of the induced subgraph H)."""
    n = len(keys)
    inner = [i for i in range(n) if level[i] <= R - 1]
    pos = array.array("i", [-1] * n)
    for j, i in enumerate(inner):
        pos[i] = j
    nb = array.array("i", [-1] * (4 * len(inner)))
    for j, i in enumerate(inner):
        g = unkey(keys[i])
        for t, s in enumerate(TGENS):
            k = key(tmul(g, s))
            m = idx[k]
            nb[4 * j + t] = pos[m]
    return inner, nb


def peel(nb, n):
    """Charikar: repeatedly delete a vertex of minimum current degree; return the
    prefix with the largest density e/|A| seen along the way, as a boolean mask."""
    deg = array.array("i", [0] * n)
    for j in range(n):
        d = 0
        base = 4 * j
        for t in range(4):
            if nb[base + t] >= 0:
                d += 1
        deg[j] = d
    edges = sum(deg) // 2
    alive = bytearray([1] * n)
    buckets = [[] for _ in range(5)]
    for j in range(n):
        buckets[deg[j]].append(j)
    size = n
    best = (edges / n, n)          # (density, size at that moment)
    order = []
    cur_edges = edges
    while size > 0:
        v = -1
        for d in range(5):
            while buckets[d]:
                cand = buckets[d].pop()
                if alive[cand] and deg[cand] == d:
                    v = cand
                    break
            if v >= 0:
                break
        if v < 0:
            break
        alive[v] = 0
        order.append(v)
        cur_edges -= deg[v]
        size -= 1
        base = 4 * v
        for t in range(4):
            u = nb[base + t]
            if u >= 0 and alive[u]:
                deg[u] -= 1
                buckets[deg[u]].append(u)
        if size > 0 and cur_edges / size > best[0]:
            best = (cur_edges / size, size)
    # rebuild the best prefix: the set alive after removing the first n-best_size
    mask = bytearray([1] * n)
    for v in order[: n - best[1]]:
        mask[v] = 0
    return mask


def count(mask, nb, n):
    """Exact (|A|, e(A)) for the induced subgraph."""
    size = 0
    twice = 0
    for j in range(n):
        if mask[j]:
            size += 1
            base = 4 * j
            for t in range(4):
                u = nb[base + t]
                if u >= 0 and mask[u]:
                    twice += 1
    assert twice % 2 == 0
    return size, twice // 2


def local_search(mask, nb, n, rounds=60, log=lambda s: None):
    """Alternate: drop every vertex whose inner degree is below the current density
    e/|A|, then add every outside vertex whose inner degree exceeds it.  Both moves
    strictly increase e/|A| when applied one at a time; applying them in batches is
    checked by recounting, and a batch that does not improve is rolled back."""
    size, e = count(mask, nb, n)
    deg = array.array("i", [0] * n)
    for j in range(n):
        d = 0
        base = 4 * j
        for t in range(4):
            u = nb[base + t]
            if u >= 0 and mask[u]:
                d += 1
        deg[j] = d
    for it in range(rounds):
        improved = False
        for phase in (0, 1):
            dens_num, dens_den = e, size
            cand = []
            for j in range(n):
                if phase == 0 and mask[j] and deg[j] * dens_den < dens_num:
                    cand.append(j)
                elif phase == 1 and not mask[j] and deg[j] * dens_den > dens_num:
                    cand.append(j)
            if not cand:
                continue
            new = bytearray(mask)
            for j in cand:
                new[j] = 1 - new[j]
            s2, e2 = count(new, nb, n)
            if s2 > 0 and e2 * size > e * s2:
                mask = new
                size, e = s2, e2
                for j in range(n):
                    d = 0
                    base = 4 * j
                    for t in range(4):
                        u = nb[base + t]
                        if u >= 0 and mask[u]:
                            d += 1
                    deg[j] = d
                improved = True
            else:
                # batch failed: apply the single best move instead
                best = None
                for j in cand:
                    if phase == 0:
                        s2, e2 = size - 1, e - deg[j]
                    else:
                        s2, e2 = size + 1, e + deg[j]
                    if s2 > 0 and (best is None or e2 * best[0] > best[1] * s2):
                        best = (s2, e2, j)
                if best and best[1] * size > e * best[0]:
                    j = best[2]
                    mask[j] = 1 - mask[j]
                    size, e = best[0], best[1]
                    for t in range(4):
                        u = nb[4 * j + t]
                        if u >= 0:
                            deg[u] += 1 if mask[j] else -1
                    improved = True
        log(f"  round {it}: |A|={size} e={e} b={(4*size-2*e)/size:.6f}")
        if not improved:
            break
    return mask, size, e


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("R", type=int)
    ap.add_argument("--out", default=None)
    ap.add_argument("--dump", default=None)
    ap.add_argument("--quiet", action="store_true")
    a = ap.parse_args()
    log = (lambda s: None) if a.quiet else (lambda s: print(s, file=sys.stderr, flush=True))

    t0 = time.time()
    keys, idx, level = build_ball(a.R, log)
    spheres = [0] * (a.R + 1)
    for l in level:
        spheres[l] += 1
    log(f"ball built in {time.time()-t0:.1f}s")
    inner, nb = adjacency(keys, idx, level, a.R)
    n = len(inner)
    log(f"induced subgraph on B_{a.R-1}: {n} vertices")

    whole = bytearray([1] * n)
    s0, e0 = count(whole, nb, n)
    res = {"R": a.R, "sphere_sizes": spheres,
           "ball_B_Rminus1": n,
           "whole_ball": {"size": s0, "edges": e0, "b": (4 * s0 - 2 * e0) / s0}}
    log(f"whole B_{a.R-1}: b = {res['whole_ball']['b']:.6f}")

    mask = peel(nb, n)
    s1, e1 = count(mask, nb, n)
    res["peeled"] = {"size": s1, "edges": e1, "b": (4 * s1 - 2 * e1) / s1}
    log(f"peeled: |A|={s1} b={res['peeled']['b']:.6f}")

    mask, s2, e2 = local_search(mask, nb, n, log=log)
    res["local_search"] = {"size": s2, "edges": e2, "b": (4 * s2 - 2 * e2) / s2}
    log(f"local search: |A|={s2} b={res['local_search']['b']:.6f}")

    best = min([res["whole_ball"], res["peeled"], res["local_search"]], key=lambda d: d["b"])
    res["best"] = best
    res["boundary_edges"] = 4 * best["size"] - 2 * best["edges"]
    res["seconds"] = round(time.time() - t0, 1)
    if a.dump:
        with open(a.dump, "w") as fh:
            for j in range(n):
                if mask[j]:
                    fh.write(f"{keys[inner[j]]}\n")
    out = json.dumps(res, indent=1)
    if a.out:
        open(a.out, "w").write(out + "\n")
    print(out)


if __name__ == "__main__":
    main()
