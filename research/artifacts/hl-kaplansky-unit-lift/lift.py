#!/usr/bin/env python3
"""Hensel lifting test for units of F_d[P] on their own support pair.

P = <a, b | (a^2)^b = a^-2, (b^2)^a = b^-2>, x = a^2, y = b^2, z = (ab)^2.
Elements of K[P] are 4-tuples (p, q, r, s) of Laurent polynomials in x, y, z,
meaning p + q a + r b + s ab.  Multiplication follows Gardam
(arXiv:2102.11818, Section 3.1), with conjugation acting on the right:
  ^a : x -> x,    y -> 1/y, z -> 1/z
  ^b : x -> 1/x,  y -> y,   z -> 1/z
  ^ab: x -> 1/x,  y -> 1/y, z -> z
  (a'a)_1  = p'p + x q' q^a + y r' r^b + z s' s^ab
  (a'a)_a  = p'q + q' p^a + x^-1 z^-1 r' s^b + y^-1 s' r^ab
  (a'a)_b  = p'r + x q' s^a + r' p^b + y^-1 z s' q^ab
  (a'a)_ab = p's + q' r^a + x^-1 y z^-1 r' q^b + s' p^ab
For a unit alpha of F_d[P] with integer lift A and inverse lift A', the
support pair (S, T) = (supp A, supp A') carries a unit modulo d^2 reducing to
(alpha, alpha^-1) iff E = (A'A - 1)/d lies mod d in the image of
L(delta, delta') = A' delta + delta' A, delta on S, delta' on T.
"""
import json
import sys

ACT = {"1": (1, 1, 1), "a": (1, -1, -1), "b": (-1, 1, -1), "ab": (-1, -1, 1)}
COMP = ["1", "a", "b", "ab"]


def P(*terms):
    out = {}
    for c, e in terms:
        out[e] = out.get(e, 0) + c
    return {k: v for k, v in out.items() if v}


def add(*fs):
    out = {}
    for f in fs:
        for k, v in f.items():
            out[k] = out.get(k, 0) + v
    return {k: v for k, v in out.items() if v}


def mul(f, h):
    out = {}
    for (i, j, k), c in f.items():
        for (i2, j2, k2), c2 in h.items():
            key = (i + i2, j + j2, k + k2)
            out[key] = out.get(key, 0) + c * c2
    return {k: v for k, v in out.items() if v}


def act(f, g):
    sx, sy, sz = ACT[g]
    return {(sx * i, sy * j, sz * k): c for (i, j, k), c in f.items()}


def mono(i, j, k, c=1):
    return {(i, j, k): c}


def scal(f, c):
    return {k: v * c for k, v in f.items() if v * c}


X, Y, Z = mono(1, 0, 0), mono(0, 1, 0), mono(0, 0, 1)
ONE = mono(0, 0, 0)
Xi, Yi, Zi = mono(-1, 0, 0), mono(0, -1, 0), mono(0, 0, -1)


def prod(al2, al):
    """al2 * al for al2 = (p',q',r',s'), al = (p,q,r,s)."""
    p2, q2, r2, s2 = al2
    p, q, r, s = al
    c1 = add(mul(p2, p), mul(mul(X, q2), act(q, "a")), mul(mul(Y, r2), act(r, "b")),
             mul(mul(Z, s2), act(s, "ab")))
    ca = add(mul(p2, q), mul(q2, act(p, "a")), mul(mul(mono(-1, 0, -1), r2), act(s, "b")),
             mul(mul(Yi, s2), act(r, "ab")))
    cb = add(mul(p2, r), mul(mul(X, q2), act(s, "a")), mul(r2, act(p, "b")),
             mul(mul(mono(0, -1, 1), s2), act(q, "ab")))
    cab = add(mul(p2, s), mul(q2, act(r, "a")), mul(mul(mono(-1, 1, -1), r2), act(q, "b")),
              mul(s2, act(p, "ab")))
    return (c1, ca, cb, cab)


def gardam_inverse(al):
    p, q, r, s = al
    return (mul(Xi, act(p, "a")), scal(mul(Xi, q), -1), scal(mul(Yi, r), -1),
            mul(Zi, act(s, "a")))


def powf(f, n):
    out = ONE
    for _ in range(n):
        out = mul(out, f)
    return out


def units():
    u = {}
    # Gardam's F_2 unit (calibration: main records no lift modulo 4 on its pair).
    u["gardam_F2"] = (2, (
        mul(mul(add(ONE, X), add(ONE, Y)), add(ONE, Zi)),
        add(mono(-1, -1, 0), X, mono(0, -1, 1), Z),
        add(ONE, X, mono(0, -1, 1), mono(1, 1, 1)),
        add(ONE, mul(add(X, Xi, Y, Yi), Zi)),
    ))
    # Murray's two F_3 units (arXiv:2106.02147, second theorem).
    zm = add(Zi, scal(Z, -1))
    q3 = add(mul(mul(add(ONE, X), add(Xi, Yi)), add(ONE, scal(Zi, -1))),
             mul(add(ONE, Yi), add(Z, scal(Zi, -1))))
    r3 = add(mul(mul(add(ONE, Yi), add(X, Y)), add(Z, scal(ONE, -1))),
             mul(add(ONE, X), add(Z, scal(Zi, -1))))
    s3 = add(scal(Z, -1), mul(add(ONE, X, Xi, Y, Yi), add(Zi, scal(ONE, -1))))
    p3 = mul(mul(add(ONE, X), add(ONE, Y)), zm)
    u["murray_F3_a"] = (3, (p3, q3, r3, s3))
    u["murray_F3_b"] = (3, (p3, act_x(q3), r3_y(r3), s3))
    # Murray's family (third theorem) for d, t, w.
    for d in (3, 5, 7):
        for t in (0, 1):
            w = 0
            h = powf(add(ONE, scal(mono(0, 0, 1 - 2 * t), -1)), d - 2)
            zt = add(mono(0, 0, t), mono(0, 0, 1 - t))
            p = mul(mul(mul(add(ONE, X), add(ONE, Y)), zt), h)
            q = mul(mono(0, 0, w), mul(add(mul(add(ONE, X), add(Xi, Yi)),
                                            mul(add(ONE, Yi), add(ONE, mono(0, 0, 2 * t - 1)))), h))
            r = mul(mono(0, 0, w), mul(add(mul(mul(add(ONE, Yi), add(X, Y)), mono(0, 0, t)),
                                            mul(add(ONE, X), zt)), h))
            s = add(mono(0, 0, 2 * t - 1), mul(add(scal(ONE, 4), X, Xi, Y, Yi), h))
            u[f"murray_family_d{d}_t{t}_w0"] = (d, (p, q, r, s))
    return u


def act_x(f):
    return {(-i, j, k): c for (i, j, k), c in f.items()}


def r3_y(f):
    return {(i, -j, k): c for (i, j, k), c in f.items()}


def modp(al, d):
    return tuple({k: v % d for k, v in f.items() if v % d} for f in al)


def is_one_mod(al, d):
    one = (ONE, {}, {}, {})
    for f, g in zip(modp(al, d), one):
        if f != {k: v % d for k, v in g.items() if v % d}:
            return False
    return True


def support(al):
    return [(c, e) for idx, c in enumerate(COMP) for e in sorted(al[idx])]


def basis_elem(c, e):
    al = [{}, {}, {}, {}]
    al[COMP.index(c)] = {e: 1}
    return tuple(al)


def rank_mod(rows, ncols, d):
    """Row-reduce a list of dict rows over F_d; return (rank, pivot rows)."""
    piv = {}
    rank = 0
    for row in rows:
        row = {k: v % d for k, v in row.items() if v % d}
        while row:
            col = min(row)
            if col in piv:
                prow = piv[col]
                f = row[col]
                for k, v in prow.items():
                    nv = (row.get(k, 0) - f * v) % d
                    if nv:
                        row[k] = nv
                    else:
                        row.pop(k, None)
            else:
                inv = pow(row[col], d - 2, d)
                row = {k: (v * inv) % d for k, v in row.items()}
                piv[col] = row
                rank += 1
                break
    return rank


def lift_test(name, d, al):
    ali = gardam_inverse(al)
    pr = prod(ali, al)
    verified = is_one_mod(pr, d)
    if not verified:
        return {"name": name, "d": d, "verified_unit_mod_d": False}
    S, T = support(al), support(ali)
    cols = [("S",) + g for g in S] + [("T",) + h for h in T]
    colidx = {c: i for i, c in enumerate(cols)}
    colmaps = {}
    for g in S:
        colmaps[("S",) + g] = prod(ali, basis_elem(*g))
    for h in T:
        colmaps[("T",) + h] = prod(basis_elem(*h), al)
    positions = {}
    Erow = {}
    one = (ONE, {}, {}, {})
    E = tuple(add(f, scal(g, -1)) for f, g in zip(pr, one))
    for idx, f in enumerate(E):
        for e, v in f.items():
            assert v % d == 0
            positions.setdefault((COMP[idx], e), len(positions))
    for c, img in colmaps.items():
        for idx, f in enumerate(img):
            for e in f:
                positions.setdefault((COMP[idx], e), len(positions))
    ncols = len(cols)
    rowsL = [dict() for _ in positions]
    for c, img in colmaps.items():
        j = colidx[c]
        for idx, f in enumerate(img):
            for e, v in f.items():
                rowsL[positions[(COMP[idx], e)]][j] = v
    rowsLE = [dict(r) for r in rowsL]
    for idx, f in enumerate(E):
        for e, v in f.items():
            rowsLE[positions[(COMP[idx], e)]][ncols] = (v // d)
    rL = rank_mod([dict(r) for r in rowsL], ncols, d)
    rLE = rank_mod(rowsLE, ncols + 1, d)
    return {"name": name, "d": d, "verified_unit_mod_d": True, "S": len(S), "T": len(T),
            "equations": len(positions), "unknowns": ncols, "rank_L": rL, "rank_L_E": rLE,
            "tangent_dim": ncols - rL, "lifts_mod_d2_on_pair": rL == rLE}


def main():
    out = []
    for name, (d, al) in units().items():
        res = lift_test(name, d, al)
        out.append(res)
        print(json.dumps(res), flush=True)
    json.dump(out, open("lift_results.json", "w"), indent=1)
    print("DONE")


if __name__ == "__main__":
    main()
