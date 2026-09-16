#!/usr/bin/env python3
"""Split-module test for the vertex groups of the CCKW trivalent triangle groups.

For a vertex group B = <x, y> (x, y of order 3, given by the vertex relators of a CCKW
presentation) compute, numerically, the character table (Burnside's algorithm on class
structure constants) and for every irreducible psi:
    f_x = <psi|<x>, 1>,  f_y = <psi|<y>, 1>,  delta = f_x + f_y - psi(1)   (trivial psi: delta := -1).
A nonzero module W with W = W^<x> (+) W^<y> is a sum of nontrivial irreducibles with delta = 0.
The split kernel S(B) is the intersection of the kernels of the delta = 0 irreducibles (S = B if none).
A faithful split module exists iff |S(B)| = 1.

Exact scope: the vertex groups occurring in experiments/cckw-vtf-certificates/cckw{334_q,334_yes,344_q,444_q}.g.
Character values are floating point; integrality of psi(1), f_x, f_y is asserted to 1e-6.
"""
import os
for _v in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ.setdefault(_v, "1")
import sys, itertools, cmath, json
import numpy as np
from sympy.combinatorics.free_groups import free_group
from sympy.combinatorics.fp_groups import FpGroup

BASE = "/home/user/group-approximation/experiments/cckw-vtf-certificates/"
FILES = ["cckw334_q.g", "cckw334_yes.g", "cckw344_q.g", "cckw444_q.g"]


def parse(fname):
    out = []
    for line in open(BASE + fname):
        line = line.strip()
        if not line.startswith("rec("):
            continue
        name = line.split('name := "')[1].split('"')[0]
        rels = line.split("rels := [")[1].rsplit("]", 1)[0]
        rels = [r.strip() for r in rels.split(", ")]
        out.append((name, rels))
    return out


def letters(word):
    return frozenset(ch for ch in word if ch in "abc")


def vertex_words(rels, pair):
    return [r for r in rels if letters(r) <= set(pair)]


def perm_elements(gens):
    n = len(gens[0])
    ident = tuple(range(n))
    elems = {ident: ()}
    frontier = [ident]
    while frontier:
        new = []
        for g in frontier:
            for i, s in enumerate(gens):
                h = tuple(s[g[k]] for k in range(n))  # apply g then s
                if h not in elems:
                    elems[h] = elems[g] + (i,)
                    new.append(h)
        frontier = new
    return list(elems.keys())


def mul(p, q):  # p then q
    return tuple(q[p[k]] for k in range(len(p)))


def inv(p):
    r = [0] * len(p)
    for i, j in enumerate(p):
        r[j] = i
    return tuple(r)


def power(p, k):
    r = tuple(range(len(p)))
    for _ in range(k):
        r = mul(r, p)
    return r


def vertex_group(words, pair):
    F, X, Y = free_group("x y")
    env = {pair[0]: X, pair[1]: Y}
    rels = [eval(w.replace("^", "**"), {}, env) for w in words]
    G = FpGroup(F, rels)
    P, T = G._to_perm_group()
    gx = tuple(T(X).array_form)
    gy = tuple(T(Y).array_form)
    n = len(gx)
    gx = tuple(list(gx) + list(range(len(gx), n)))
    return gx, gy


def character_table(elems):
    idx = {g: i for i, g in enumerate(elems)}
    N = len(elems)
    cls_of = [-1] * N
    classes = []
    for i, g in enumerate(elems):
        if cls_of[i] >= 0:
            continue
        c = set()
        for h in elems:
            c.add(idx[mul(mul(inv(h), g), h)])
        for j in c:
            cls_of[j] = len(classes)
        classes.append(sorted(c))
    k = len(classes)
    a = np.zeros((k, k, k))
    for l in range(k):
        z = elems[classes[l][0]]
        for i in range(k):
            for u in classes[i]:
                v = mul(inv(elems[u]), z)  # u * v = z in the "u then v" convention
                a[i, cls_of[idx[v]], l] += 1
    rng = np.random.default_rng(1)
    M = sum(rng.normal() * a[i] for i in range(k))
    vals, vecs = np.linalg.eig(M)
    ident = cls_of[idx[tuple(range(len(elems[0])))]]
    sizes = np.array([len(c) for c in classes], dtype=float)
    chars = []
    for t in range(k):
        w = vecs[:, t] / vecs[ident, t]
        d2 = N / np.sum(np.abs(w) ** 2 / sizes)
        d = np.sqrt(d2)
        assert abs(d - round(d)) < 1e-6, d
        chars.append(d * w / sizes)
    X = np.array(chars)  # rows: irreducibles, columns: classes
    # orthogonality check
    G = (X * sizes) @ X.conj().T / N
    assert np.allclose(G, np.eye(k), atol=1e-6)
    return classes, cls_of, idx, X, ident


def analyse(gx, gy):
    elems = perm_elements([gx, gy])
    N = len(elems)
    classes, cls_of, idx, X, ident = character_table(elems)
    cx = [cls_of[idx[power(gx, j)]] for j in range(3)]
    cy = [cls_of[idx[power(gy, j)]] for j in range(3)]
    w = cmath.exp(2j * cmath.pi / 3)
    rows = []
    split_kernel = set(range(len(classes)))  # classes in the kernel intersection
    any_split = False
    for t in range(X.shape[0]):
        psi = X[t]
        d = int(round(psi[ident].real))
        fx = sum(psi[c] for c in cx).real / 3
        fy = sum(psi[c] for c in cy).real / 3
        trivial = np.allclose(psi, 1)
        delta = -1 if trivial else int(round(fx + fy - d))
        mw = sum(psi[cx[j]] * w ** (-j) for j in range(3)) / 3   # multiplicity of eigenvalue w for x
        kern = {l for l in range(len(classes)) if abs(psi[l] - d) < 1e-6}
        if delta == 0:
            any_split = True
            split_kernel &= kern
        rows.append(dict(dim=d, fx=int(round(fx)), fy=int(round(fy)), delta=delta,
                         mult_x_omega=int(round(mw.real)), kernel_order=sum(len(classes[l]) for l in kern)))
    S = sum(len(classes[l]) for l in split_kernel) if any_split else N
    return dict(order=N, nclasses=len(classes), irreps=rows, split_kernel_order=S)


def main():
    cache = {}
    report = {}
    for f in FILES:
        for name, rels in parse(f):
            labs = []
            for pair in [("a", "b"), ("b", "c"), ("c", "a")]:
                ws = vertex_words(rels, pair)
                key = tuple(sorted(w.replace(pair[0], "x").replace(pair[1], "y") for w in ws))
                if key not in cache:
                    gx, gy = vertex_group(ws, pair)
                    cache[key] = analyse(gx, gy)
                r = cache[key]
                labs.append((2 * r["order"] // 3, r["split_kernel_order"]))
            report[f + ":" + name] = labs
            print(f, name, "vertex (label, |split kernel|):", labs,
                  "ALL SPLIT-FAITHFUL" if all(s == 1 for _, s in labs) else "")
    print("\nDistinct vertex group presentations analysed:", len(cache))
    for key, r in cache.items():
        print("label", 2 * r["order"] // 3, "order", r["order"], "classes", r["nclasses"],
              "|S|", r["split_kernel_order"], "relators", key)
        for row in r["irreps"]:
            if row["delta"] == 0:
                print("    delta=0 irrep:", row)
        print("    dims of all irreps:", sorted(row["dim"] for row in r["irreps"]),
              "max delta over nontrivial:", max(row["delta"] for row in r["irreps"] if row["dim"] >= 1))
    json.dump(dict(report={k: v for k, v in report.items()},
                   vertex={str(k): v for k, v in cache.items()}),
              open("/home/user/group-approximation/experiments/split-module-triangles-2026-09-16/vertex_split.json", "w"), indent=1)


if __name__ == "__main__":
    main()
