#!/usr/bin/env python3
"""Autograd search for exotic near-solutions of PSL_2(Z[1/2]) = <x,y,x',y' | ...>.

Relations (two copies of PSL_2(Z) = <S, ST> glued along Gamma_0(2)):
    x^2 = y^3 = x'^2 = y'^3 = 1,
    x y = (x' y')^2,                    (T = T'^2)
    x y^2 x y x = x' y' x' y'^2 x'.     (eps = sigma(eps))
Sanity: for the permutation representation rho of PSL_2(F_p) on P^1(F_p), the tuple
    x = rho(S), y = rho(ST), x' = rho(t S t^-1), y' = rho(t ST t^-1),  t = diag(2,1),
must satisfy all relations exactly (this checks the presentation).
Search: unitaries parametrized as exp(skew) conjugating fixed spectral models taken from the
congruence tuple itself (so congruence solutions lie in the search space); minimize the two
gluing defects (normalized HS) by Adam from random starts; report final defects, the
congruence indicator min_{m odd} ||T^m - 1||_2, and distance-like diagnostics.
"""

from __future__ import annotations

import json
import math
import argparse
import sys
import time

import torch

torch.set_default_dtype(torch.float64)


def perm_rep_P1(p):
    pts = [(1, x % p) for x in range(p)] + [(0, 1)]
    index = {pt: i for i, pt in enumerate(pts)}

    def normalize(a, b):
        a %= p
        b %= p
        if a != 0:
            inv = pow(a, -1, p)
            return (1, (b * inv) % p)
        return (0, 1)

    def rho(g):
        d = len(pts)
        M = torch.zeros((d, d), dtype=torch.complex128)
        for (a, b), i in index.items():
            a2 = (g[0][0] * a + g[0][1] * b) % p
            b2 = (g[1][0] * a + g[1][1] * b) % p
            M[index[normalize(a2, b2)], i] = 1.0
        return M

    return rho, len(pts)


def hs(A):
    d = A.shape[0]
    return torch.sqrt(torch.real(torch.trace(A.conj().T @ A)) / d)


def defects(x, y, xp, yp):
    T = x @ y
    Tp = xp @ yp
    r1 = T - Tp @ Tp
    eps = x @ y @ y @ x @ y @ x
    epsp = xp @ yp @ xp @ yp @ yp @ xp
    return hs(r1), hs(eps - epsp)


def cong_indicator(x, y):
    d = x.shape[0]
    T = x @ y
    I = torch.eye(d, dtype=torch.complex128)
    P = I.clone()
    best, bm = 9.0, None
    for m in range(1, 4 * d + 2):
        P = P @ T
        if m % 2 == 1:
            v = float(hs(P - I))
            if v < best:
                best, bm = v, m
    return best, bm


def spectral_model(U):
    ev = torch.linalg.eigvals(U)
    return torch.diag(ev)


def unitary(K):
    K = K - K.conj().T
    return torch.linalg.matrix_exp(K)


def search(Dx, Dy, d, restarts, steps, lr, rng_seed, tag):
    torch.manual_seed(rng_seed)
    out = []
    for r in range(restarts):
        params = [torch.randn(d, d, dtype=torch.complex128, requires_grad=True) for _ in range(4)]
        with torch.no_grad():
            for P in params:
                P *= 0.8
        opt = torch.optim.Adam(params, lr=lr)
        best = 9.0
        for it in range(steps):
            opt.zero_grad()
            Vs = [unitary(P) for P in params]
            x = Vs[0] @ Dx @ Vs[0].conj().T
            y = Vs[1] @ Dy @ Vs[1].conj().T
            xp = Vs[2] @ Dx @ Vs[2].conj().T
            yp = Vs[3] @ Dy @ Vs[3].conj().T
            a, b = defects(x, y, xp, yp)
            loss = a * a + b * b
            loss.backward()
            opt.step()
            if it % 500 == 0 and it > 0:
                for g in opt.param_groups:
                    g["lr"] *= 0.7
        with torch.no_grad():
            Vs = [unitary(P) for P in params]
            x = Vs[0] @ Dx @ Vs[0].conj().T
            y = Vs[1] @ Dy @ Vs[1].conj().T
            xp = Vs[2] @ Dx @ Vs[2].conj().T
            yp = Vs[3] @ Dy @ Vs[3].conj().T
            a, b = defects(x, y, xp, yp)
            ci, cm = cong_indicator(x, y)
            trT = torch.trace(x @ y) / d
            rec = {"tag": tag, "d": d, "restart": r, "defect1": float(a), "defect2": float(b),
                   "cong_ind": ci, "cong_m": cm, "trT": [float(trT.real), float(trT.imag)]}
            out.append(rec)
            print(json.dumps(rec))
            sys.stdout.flush()
    return out


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--sanity-only", action="store_true",
                        help="check exact congruence tuples and skip optimization")
    parser.add_argument("--primes", default="11,13,17,23,29")
    parser.add_argument("--restarts", type=int, default=None)
    parser.add_argument("--steps", type=int, default=None)
    parser.add_argument("--output", default="psl2-half-exotic-torch.json")
    args = parser.parse_args()
    results = []
    t0 = time.time()
    for p in tuple(int(x) for x in args.primes.split(",") if x):
        rho, d = perm_rep_P1(p)
        inv2 = pow(2, -1, p)
        S = [[0, -1], [1, 0]]
        ST = [[0, -1], [1, 1]]
        # second copy = t^-1 V_1 t with t = diag(2,1): t^-1 S t = [[0,-1/2],[2,0]], t^-1 ST t = [[0,-1/2],[2,1]]
        tSt = [[0, (-inv2) % p], [2, 0]]
        tSTt = [[0, (-inv2) % p], [2, 1]]
        x, y, xp, yp = rho(S), rho(ST), rho(tSt), rho(tSTt)
        a, b = defects(x, y, xp, yp)
        ord_chk = [float(hs(x @ x - torch.eye(d, dtype=torch.complex128))),
                   float(hs(y @ y @ y - torch.eye(d, dtype=torch.complex128))),
                   float(hs(xp @ xp - torch.eye(d, dtype=torch.complex128))),
                   float(hs(yp @ yp @ yp - torch.eye(d, dtype=torch.complex128)))]
        ci, cm = cong_indicator(x, y)
        sanity = {"tag": "congruence-sanity", "p": p, "d": d, "defect1": float(a), "defect2": float(b),
                  "orders": ord_chk, "cong_ind": ci, "cong_m": cm}
        print(json.dumps(sanity))
        sys.stdout.flush()
        results.append(sanity)
        if args.sanity_only:
            continue
        Dx, Dy = spectral_model(x), spectral_model(y)
        # also a balanced (regular-like) spectral model
        if d % 6 == 0 or True:
            k2 = d // 2
            Dxb = torch.diag(torch.tensor([1.0] * k2 + [-1.0] * (d - k2), dtype=torch.complex128))
            w = complex(math.cos(2 * math.pi / 3), math.sin(2 * math.pi / 3))
            k3 = d // 3
            Dyb = torch.diag(torch.tensor([1.0] * (d - 2 * k3) + [w] * k3 + [w * w] * k3, dtype=torch.complex128))
        restarts = args.restarts if args.restarts is not None else (6 if p <= 13 else 4)
        steps = args.steps if args.steps is not None else (3000 if p <= 13 else 2500)
        results += search(Dx, Dy, d, restarts, steps, 0.02, 100 + p, f"congruence-spectra-p{p}")
        results += search(Dxb, Dyb, d, restarts, steps, 0.02, 200 + p, f"balanced-spectra-d{d}")
        print(f"# elapsed {time.time()-t0:.0f}s")
        sys.stdout.flush()
    with open(args.output, "w") as fh:
        json.dump(results, fh, indent=1)
    print("DONE-SENTINEL")


if __name__ == "__main__":
    main()
