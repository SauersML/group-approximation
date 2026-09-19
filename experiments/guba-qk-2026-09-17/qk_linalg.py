#!/usr/bin/env python3
"""Exact mod-p search for nonzero solutions of Guba's system Q_k in K[M].

Q_k:  t_0 u_0 = t_1 u_1 = ... = t_k u_k,   t_i = a_i x_0 + b_i x_1 + c_i x_2,
with u_i homogeneous of degree n in K[M], M the positive monoid of Thompson's F.

Search space: u_i in V = K[M_(n,L)] (normal forms of degree n, letters <= L), L >= n + 2,
so that x_j V lies in A = K[M_(n+1,L)] for j = 0, 1, 2.

Method.  For each i >= 1 with c_i != 0, rho_i : A -> K[C] is the linear map defined by
  rho_i(m) = m                                        if m is not of the form x_2 w,
  rho_i(x_2 w) = -(a_i rho_i(x_0 w) + b_i rho_i(x_1 w)) / c_i.
C = monomials of A not left-divisible by x_2.  The recursion is well founded: in a bi-order of F
with x_0, x_1 < x_2 (germ at the left end of the support) x_0 w, x_1 w < x_2 w.  rho_i is the
identity on K[C] and kills t_i V, and |C| + |V| = |A|, so ker rho_i = t_i V.
Hence a solution with u_0 in V exists iff the map u_0 -> (rho_i(t_0 u_0))_i has a kernel.
The script prints the kernel dimension and, with --verify, recovers u_1..u_k by the matching
quotient recursion and checks t_i u_i = t_0 u_0 by direct multiplication.
"""
import argparse, itertools, random, sys
import numpy as np
import flint

sys.setrecursionlimit(1_000_000)


def left_mult(j, w):
    """Normal form of x_j w (Step 1 of the tower-degree proof)."""
    n = len(w)
    k = 0
    while k < n and w[k] < j + k:
        k += 1
    return w[:k] + (j + k,) + w[k:]


def x2_quotient(m):
    """w with x_2 w = m, or None."""
    n = len(m)
    k = 0
    while k < n and m[k] < 2 + k:
        k += 1
    if k == n or m[k] != 2 + k:
        return None
    w = m[:k] + m[k + 1:]
    return w


def monomials(n, L):
    return list(itertools.combinations_with_replacement(range(L + 1), n))


def build(k, n, L, forms, p, verify=False):
    V = monomials(n, L)
    A = monomials(n + 1, L)
    Vidx = {w: i for i, w in enumerate(V)}
    Aidx = {m: i for i, m in enumerate(A)}
    C = [m for m in A if x2_quotient(m) is None]
    Cidx = {m: i for i, m in enumerate(C)}
    assert len(C) + len(V) == len(A)
    a0, b0, c0 = forms[0]
    blocks = []
    quots = []
    for i in range(1, k + 1):
        a, b, c = forms[i]
        assert c % p != 0
        cinv = pow(c, p - 2, p)
        rho = {}
        q = {} if verify else None

        def get(m):
            if m in rho:
                return rho[m]
            w = x2_quotient(m)
            if w is None:
                v = np.zeros(len(C), dtype=np.int64)
                v[Cidx[m]] = 1
                rho[m] = v
                if verify:
                    q[m] = {}
                return v
            r0 = get(left_mult(0, w))
            r1 = get(left_mult(1, w))
            v = (-(a * r0 + b * r1) % p) * cinv % p
            rho[m] = v
            if verify:
                qq = {w: cinv}
                for coef, mm in ((a, left_mult(0, w)), (b, left_mult(1, w))):
                    for key, val in q[mm].items():
                        qq[key] = (qq.get(key, 0) - coef * cinv * val) % p
                q[m] = {kk: vv for kk, vv in qq.items() if vv}
            return v

        R = np.zeros((len(C), len(V)), dtype=np.int64)
        for col, w in enumerate(V):
            R[:, col] = (a0 * get(left_mult(0, w)) + b0 * get(left_mult(1, w))
                         + c0 * get(left_mult(2, w))) % p
        blocks.append(R)
        quots.append(q)
    return V, A, C, blocks, quots


def mat_rank(R, p):
    M = flint.nmod_mat(R.shape[0], R.shape[1], [int(x) for x in R.flatten()], p)
    return M.rank(), M


def kernel_vector(R, p):
    Mt = flint.nmod_mat(R.shape[0], R.shape[1], [int(x) for x in R.flatten()], p)
    X, nullity = Mt.nullspace()
    return X, nullity


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("k", type=int)
    ap.add_argument("n", type=int)
    ap.add_argument("L", type=int)
    ap.add_argument("--p", type=int, default=1000003)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--forms", type=str, default="")
    ap.add_argument("--verify", action="store_true")
    args = ap.parse_args()
    p = args.p
    if args.forms:
        forms = [tuple(int(x) % p for x in f.split(",")) for f in args.forms.split(";")]
    else:
        rng = random.Random(args.seed)
        forms = [tuple(rng.randrange(1, p) for _ in range(3)) for _ in range(args.k + 1)]
    assert len(forms) == args.k + 1 and args.L >= args.n + 2
    V, A, C, blocks, quots = build(args.k, args.n, args.L, forms, p, args.verify)
    R = np.vstack(blocks)
    X, nullity = kernel_vector(R, p)
    print(f"k={args.k} n={args.n} L={args.L} p={p} |V|={len(V)} |A|={len(A)} |C|={len(C)} "
          f"rows={R.shape[0]} kernel_dim={nullity}", flush=True)
    if args.verify and nullity > 0:
        u0 = {V[r]: int(X[r, 0]) for r in range(len(V)) if int(X[r, 0])}

        def mult(t, u):
            out = {}
            for coef, j in zip(t, (0, 1, 2)):
                for w, c in u.items():
                    m = left_mult(j, w)
                    out[m] = (out.get(m, 0) + coef * c) % p
            return {m: c for m, c in out.items() if c}

        target = mult(forms[0], u0)
        ok = True
        for i in range(1, args.k + 1):
            q = quots[i - 1]
            ui = {}
            for m, c in target.items():
                for w, val in q[m].items():
                    ui[w] = (ui.get(w, 0) + c * val) % p
            ui = {w: c for w, c in ui.items() if c}
            ok = ok and mult(forms[i], ui) == target and len(ui) > 0
        print(f"verify: |supp u0|={len(u0)} |supp w|={len(target)} all t_i u_i = w: {ok}")


if __name__ == "__main__":
    main()
