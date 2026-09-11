#!/usr/bin/env python3
"""CNF for a sigma-invariant W(q) triangle table (sigma from w8model.py).

A triangle table (the `Table 585 1755` of `KazhdanHypGQEightTableFormat.lean`
at q = 8) is a bijection lambda : points -> lines and a set of rows (x,y,z) with
  y in lambda(x),  z in lambda(y),  x in lambda(z),
such that every arc (x,y) with y in lambda(x) is the corner of exactly one row,
and rows are closed under rotation.  The search asks the table to be invariant
under sigma, so lambda is sigma-equivariant.  With sigma of order 1 there is no
symmetry assumption (the W(2) calibration).

Variables
  A(i,j,k)  lambda(x_i) = sigma^k l_j           (x_i, l_j orbit representatives)
  E(i,p)    arc x_i -> p, i.e. p in lambda(x_i)  (arcs normalized by sigma)
  D(c)      the triangle class c is a row        (rotation classes of
            normalized triples (x_i, p, r); a class covers its three arcs)
Constraints
  exactly one (j,k) for each i and one (i,k) for each j  (lambda bijective)
  E(i,p) <-> OR over the lines m through p of A(i, j(m), b(m))
  D(c) -> E of each of its three arcs
  E(i,p) -> at least one r with D(class(x_i,p,r)); at most one such r
The cube (x_i,x_i,x_i) is excluded.  A class whose triangle has two corners in
the same sigma-orbit of arcs appears twice in one at-most-one list and is thereby
forbidden, which is exactly what exact cover by sigma-translates requires.

Usage: w8encode.py <model.json> <out.cnf> <out.map.json>
"""
import json
import os
import sys


def main():
    model = json.load(open(sys.argv[1]))
    cnf_path, map_path = sys.argv[2], sys.argv[3]
    N = len(model["points"])
    R = model.get("order", 65)
    assert N % R == 0
    O = N // R
    sp = model["sigma_points"]
    sl = model["sigma_lines"]
    point_lines = model["point_lines"]
    spow = [list(range(N))]
    for _ in range(1, R):
        spow.append([sp[x] for x in spow[-1]])
    lpow = [list(range(N))]
    for _ in range(1, R):
        lpow.append([sl[x] for x in lpow[-1]])

    def orbit_data(pw):
        reps, idx, exp = [], [None] * N, [None] * N
        for s in range(N):
            if idx[s] is not None:
                continue
            reps.append(s)
            for k in range(R):
                x = pw[k][s]
                assert idx[x] is None
                idx[x], exp[x] = len(reps) - 1, k
        assert len(reps) == O
        return reps, idx, exp

    preps, ip, ap = orbit_data(spow)
    lreps, jl, bl = orbit_data(lpow)

    def A(i, j, k):
        return 1 + (i * O + j) * R + k

    E0 = 1 + O * O * R

    def E(i, p):
        return E0 + i * N + p

    nxt = [E0 + O * N]

    def fresh():
        v = nxt[0]
        nxt[0] += 1
        return v

    body = open(cnf_path + ".body", "w")
    ncl = [0]

    def clause(lits):
        body.write(" ".join(map(str, lits)) + " 0\n")
        ncl[0] += 1

    def amo(lits):
        n = len(lits)
        if n <= 1:
            return
        if n <= 6:
            for a in range(n):
                for b in range(a + 1, n):
                    clause([-lits[a], -lits[b]])
            return
        s = [fresh() for _ in range(n - 1)]
        clause([-lits[0], s[0]])
        for k in range(1, n - 1):
            clause([-lits[k], s[k]])
            clause([-s[k - 1], s[k]])
            clause([-lits[k], -s[k - 1]])
        clause([-lits[n - 1], -s[n - 2]])

    def exactly_one(lits):
        clause(lits)
        amo(lits)

    for i in range(O):
        exactly_one([A(i, j, k) for j in range(O) for k in range(R)])
    for j in range(O):
        exactly_one([A(i, j, k) for i in range(O) for k in range(R)])
    for i in range(O):
        for p in range(N):
            terms = [A(i, jl[m], bl[m]) for m in point_lines[p]]
            clause([-E(i, p)] + terms)
            for t in terms:
                clause([-t, E(i, p)])

    def key(i, p, r):
        return (i * N + p) * N + r

    def unkey(k):
        return k // (N * N), (k // N) % N, k % N

    def rot(i, p, r):
        back = spow[(R - ap[p]) % R]
        return ip[p], back[r], back[preps[i]]

    def arcs(i, p, r):
        return (E(i, p),
                E(ip[p], spow[(R - ap[p]) % R][r]),
                E(ip[r], spow[(R - ap[r]) % R][preps[i]]))

    cls = {}
    arclists = [[] for _ in range(O * N)]
    for i in range(O):
        xi = preps[i]
        for p in range(N):
            lst = arclists[i * N + p]
            for r in range(N):
                if p == xi and r == xi:
                    continue
                t0 = (i, p, r)
                t1 = rot(*t0)
                t2 = rot(*t1)
                c = min(key(*t0), key(*t1), key(*t2))
                v = cls.get(c)
                if v is None:
                    v = fresh()
                    cls[c] = v
                    for e in arcs(*unkey(c)):
                        clause([-v, e])
                lst.append(v)
    for i in range(O):
        for p in range(N):
            lst = arclists[i * N + p]
            clause([-E(i, p)] + lst)
            amo(lst)
    body.close()
    nvars = nxt[0] - 1
    with open(cnf_path, "w") as fh:
        fh.write(f"p cnf {nvars} {ncl[0]}\n")
        with open(cnf_path + ".body") as b:
            for line in b:
                fh.write(line)
    os.remove(cnf_path + ".body")
    json.dump({"N": N, "R": R, "O": O, "E0": E0, "point_reps": preps,
               "line_reps": lreps,
               "classes": {str(v): k for k, v in cls.items()}}, open(map_path, "w"))
    print(f"cnf: {nvars} variables, {ncl[0]} clauses, {len(cls)} triangle classes")


if __name__ == "__main__":
    main()
