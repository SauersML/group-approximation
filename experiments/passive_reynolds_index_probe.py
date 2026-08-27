#!/usr/bin/env python3
"""Sparse-combinatorial probe of the scalar Reynolds column (DSS3).

The script never materializes the tall column C.  It accumulates C^T C,
solves one equivariant Green column, and evaluates ||C(C^T C)^dagger e||_1.
That number is the induced infinity norm of the Moore--Penrose inverse when
the sign-induced input action is transitive.
"""

import argparse
import os

os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("OMP_NUM_THREADS", "1")

import numpy as np


def mul(x, y, p):
    a, b, c, d = x
    e, f, g, h = y
    return ((a * e + b * g) % p, (a * f + b * h) % p,
            (c * e + d * g) % p, (c * f + d * h) % p)


def inv(x, p):
    a, b, c, d = x
    return (d, -b % p, -c % p, a)


def canon(x, p):
    y = tuple((-a) % p for a in x)
    return min(x, y)


def sl2_projective(p):
    out = set()
    for a in range(p):
        for b in range(p):
            if a:
                ai = pow(a, p - 2, p)
                for c in range(p):
                    d = ((1 + b * c) * ai) % p
                    out.add(canon((a, b, c, d), p))
            elif b:
                c = -pow(b, p - 2, p) % p
                for d in range(p):
                    out.add(canon((a, b, c, d), p))
    return sorted(out)


def build_column_rows(p):
    one = canon((1, 0, 0, 1), p)
    r = canon((2 % p, 0, 0, pow(2, p - 2, p)), p)
    s = canon((1, pow(2, p - 2, p), 0, 1), p)
    x = canon((0, -1 % p, 1, 0), p)
    a = canon(mul(x, mul(s, s, p), p), p)
    b = canon(mul(mul(x, r, p), s, p), p)

    group = sl2_projective(p)
    index = {q: i for i, q in enumerate(group)}
    assert one in index

    h = []
    z = one
    while not h or z != one:
        h.append(z)
        z = canon(mul(z, r, p), p)

    # Each left H-coset gets a representative.  Pair it with its w-translate;
    # the smaller coset id is the positive side of one sign-induced coordinate.
    coset = [-1] * len(group)
    cosets = []
    for qi, q in enumerate(group):
        if coset[qi] >= 0:
            continue
        cid = len(cosets)
        members = []
        for hh in h:
            j = index[canon(mul(hh, q, p), p)]
            coset[j] = cid
            members.append(j)
        cosets.append(members)
    mate = [None] * len(cosets)
    for cid, members in enumerate(cosets):
        q = group[members[0]]
        mate[cid] = coset[index[canon(mul(x, q, p), p)]]
        assert mate[cid] != cid

    coord = [None] * len(cosets)
    n = 0
    for cid in range(len(cosets)):
        if coord[cid] is not None:
            continue
        other = mate[cid]
        coord[cid] = (n, 1)
        coord[other] = (n, -1)
        n += 1

    def term(g):
        rows = []
        for q in group:
            v = canon(mul(g, q, p), p)
            rows.append(coord[coset[index[v]]])
        return rows

    a1, a2 = inv(a, p), mul(inv(a, p), inv(a, p), p)
    b1, b2 = inv(b, p), mul(inv(b, p), inv(b, p), p)
    s2 = mul(s, s, p)
    first = [term(s2), term(mul(s2, a1, p)), term(mul(s2, a2, p))]
    second = [term(s), term(mul(s, b1, p)), term(mul(s, b2, p))]
    return len(group), len(h), n, first + second


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("primes", nargs="+", type=int)
    ap.add_argument("--iterative", action="store_true")
    ap.add_argument("--steps", type=int, default=800)
    args = ap.parse_args()
    for p in args.primes:
        qsize, hsize, n, terms = build_column_rows(p)
        packed = []
        for block in (terms[:3], terms[3:]):
            js = np.empty((qsize, 3), dtype=np.int32)
            ss = np.empty((qsize, 3), dtype=np.float64)
            for t, data in enumerate(block):
                js[:, t] = [z[0] for z in data]
                ss[:, t] = [z[1] for z in data]
            packed.append((js, ss))

        def apply_c(v):
            return [np.sum(ss * v[js], axis=1) for js, ss in packed]

        def apply_ct(ys):
            out = np.zeros(n)
            for (js, ss), y in zip(packed, ys):
                for t in range(3):
                    out += np.bincount(js[:, t], weights=ss[:, t] * y,
                                       minlength=n)
            return out

        def apply_normal(v):
            return apply_ct(apply_c(v))

        if args.iterative:
            v = np.ones(n) / np.sqrt(n)
            for _ in range(30):
                v = apply_normal(v)
                v /= np.linalg.norm(v)
            top = float(v @ apply_normal(v))
            tau = 0.9 / top
            rhs = np.zeros(n)
            rhs[0] = 1.0
            green = np.zeros(n)
            old = None
            for step in range(1, args.steps + 1):
                green += tau * (rhs - apply_normal(green))
                if step in (50, 100, 200, 400, 800, args.steps):
                    l1 = sum(float(np.abs(y).sum()) for y in apply_c(green))
                    delta = float("nan") if old is None else l1 - old
                    print("iter", p, step, f"{top:.9g}", f"{l1:.9g}",
                          f"{delta:.3g}", flush=True)
                    old = l1
            torus = (p - 1) // 2
            print(p, qsize, hsize, torus // hsize, n, "iter", "-", "-",
                  f"{l1:.9g}", flush=True)
            continue

        normal = np.zeros((n, n), dtype=np.float64)
        # Three terms per output block.  Combine collisions before adding rr^T.
        for block in (terms[:3], terms[3:]):
            for qi in range(qsize):
                row = {}
                for data in block:
                    j, sign = data[qi]
                    row[j] = row.get(j, 0) + sign
                items = [(j, v) for j, v in row.items() if v]
                for j, v in items:
                    for k, w in items:
                        normal[j, k] += v * w
        vals, vecs = np.linalg.eigh(normal)
        cutoff = max(vals[-1], 1.0) * 1e-10
        nz = vals > cutoff
        rhs = np.zeros(n)
        rhs[0] = 1.0
        green = vecs[:, nz] @ ((vecs[:, nz].T @ rhs) / vals[nz])
        l1 = 0.0
        for block in (terms[:3], terms[3:]):
            for qi in range(qsize):
                value = 0.0
                for data in block:
                    j, sign = data[qi]
                    value += sign * green[j]
                l1 += abs(value)
        torus = (p - 1) // 2
        print(p, qsize, hsize, torus // hsize, n, int(nz.sum()),
              f"{vals[nz][0] ** 0.5:.9g}", f"{vals[-1] ** 0.5:.9g}",
              f"{l1:.9g}", flush=True)


if __name__ == "__main__":
    main()
