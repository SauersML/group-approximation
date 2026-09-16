#!/usr/bin/env python3
"""Hand-checkable certificate that some torsion orbit has Stab contained in p Gamma.

Setting as in stabilizers.py: Gamma = <M_a, M_b> = Z^2 acting on T^3, torsion
point chi_v of order N, gamma fixes chi_v iff M_gamma^T v = v mod N.

Certificate for "Stab(v) is contained in p Z^2":
  (i)  L is a common multiple with (M_a^T)^L = I = (M_b^T)^L mod N and p | L,
       so L Z^2 is contained in Stab(v);
  (ii) for every nonzero eps in {0,...,p-1}^2,
       (M_a^T)^{(L/p) eps_1} (M_b^T)^{(L/p) eps_2} v != v mod N.
If (n,m) in Stab(v) with (n,m) not in p Z^2, then (L/p)(n,m) in Stab(v) and
(L/p)(n,m) = (L/p)(n mod p, m mod p) mod L Z^2, contradicting (ii).

The script prints the matrices appearing in (i) and the vectors in (ii), so
the certificate can be rechecked by hand or in any CAS.  It also recomputes
the preimage family: if p^j w = v then Stab(w) <= Stab(v), so infinitely many
distinct orbits have Stab <= p Z^2.  Single-threaded integer arithmetic.
"""
import json
import sys

MA = ((0, 0, 1), (1, 0, 2), (0, 1, -1))
MB_MINUS = ((1, 0, 1), (1, 1, 2), (0, 1, 0))
MB_PLUS = tuple(tuple(-x for x in row) for row in MB_MINUS)


def mat_mul(X, Y, mod):
    return tuple(
        tuple(sum(X[i][k] * Y[k][j] for k in range(3)) % mod for j in range(3))
        for i in range(3)
    )


def mat_pow(X, e, mod):
    R = tuple(tuple((1 % mod) if i == j else 0 for j in range(3)) for i in range(3))
    B = tuple(tuple(x % mod for x in row) for row in X)
    while e:
        if e & 1:
            R = mat_mul(R, B, mod)
        B = mat_mul(B, B, mod)
        e >>= 1
    return R


def transpose(X):
    return tuple(tuple(X[j][i] for j in range(3)) for i in range(3))


def apply(X, v, N):
    return tuple(sum(X[i][k] * v[k] for k in range(3)) % N for i in range(3))


def certify(sign, MB, p, N, v, L):
    At, Bt = transpose(MA), transpose(MB)
    ident = tuple(tuple((1 % N) if i == j else 0 for j in range(3)) for i in range(3))
    AL, BL = mat_pow(At, L, N), mat_pow(Bt, L, N)
    assert L % p == 0
    part_i = {"L": L, "At^L_mod_N": AL, "Bt^L_mod_N": BL,
              "both_identity": AL == ident and BL == ident}
    assert part_i["both_identity"]
    q = L // p
    part_ii = []
    for e1 in range(p):
        for e2 in range(p):
            if (e1, e2) == (0, 0):
                continue
            w = apply(mat_pow(At, q * e1, N), apply(mat_pow(Bt, q * e2, N), v, N), N)
            part_ii.append({"eps": [e1, e2], "image": w, "differs_from_v": w != tuple(x % N for x in v)})
            assert w != tuple(x % N for x in v)
    # basis vectors reported by stabilizers.py really fix v (sanity only)
    return {"sign": sign, "p": p, "N": N, "v": v, "part_i": part_i, "part_ii": part_ii,
            "conclusion": f"Stab(v) <= {p} Z^2"}


def preimage_family(MB, p, N, v, levels):
    """w_j = v/p^j viewed in (Z/(N p^j))^3; check Stab(w_j) <= Stab(v) in a finite window."""
    At, Bt = transpose(MA), transpose(MB)
    out = []
    for j in range(1, levels + 1):
        Nj = N * p ** j
        # w_j := v as a vector mod Nj represents chi_v^{1/p^j}: p^j * (v/Nj) = v/N
        w = tuple(x % Nj for x in v)
        # any gamma fixing w mod Nj fixes v mod N, since reduction mod N commutes with M^T
        for n in range(0, 20):
            for m in range(0, 20):
                x = apply(mat_pow(At, n, Nj), apply(mat_pow(Bt, m, Nj), w, Nj), Nj)
                if x == w:
                    y = apply(mat_pow(At, n, N), apply(mat_pow(Bt, m, N), v, N), N)
                    assert y == tuple(c % N for c in v)
        out.append({"j": j, "order": Nj, "window_checked": "0<=n,m<20"})
    return out


def main():
    info = {"certificates": [], "preimage_windows": []}
    cases = [
        ("b_minus=a+1", MB_MINUS, 2, 4, (0, 0, 1), 14),
        ("b_plus=-(a+1)", MB_PLUS, 2, 4, (0, 0, 1), 14),
        ("b_minus=a+1", MB_MINUS, 3, 9, (0, 0, 1), 78),
        ("b_plus=-(a+1)", MB_PLUS, 3, 9, (0, 0, 1), 39),
    ]
    for sign, MB, p, N, v, L in cases:
        info["certificates"].append(certify(sign, MB, p, N, v, L))
    info["preimage_windows"].append(preimage_family(MB_MINUS, 2, 4, (0, 0, 1), 2))
    json.dump(info, sys.stdout, indent=1)
    print()


if __name__ == "__main__":
    main()
