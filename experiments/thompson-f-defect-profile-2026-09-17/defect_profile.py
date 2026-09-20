#!/usr/bin/env python3
"""Fixed-separation Hilbert--Schmidt defect profiles, Thompson's F against sofic (BG) and open (H4) calibrations.

For a finitely presented group G = <gens | rels> and a separating word s (an element that is
trivial in every finite-dimensional unitary representation of G, but nontrivial in G), put

    e(X) = ||X - I||_2^2 = 2 - 2 Re tr_n(X)      (normalized HS),
    D_n(tau) = inf { max_r e(r(U)) : U in U(n)^gens, e(s(U)) >= tau }.

G has HS models separating s (for Thompson's F with s = [a,b]: G is hyperlinear) iff
D_n(tau) -> 0 along n for some tau > 0 (up to the usual passage to subsequences).

Groups:
  F  : <a,b | [ab^-1, a^-1ba], [ab^-1, a^-2ba^2]>,  s = [a,b].   Finite-dimensional unitary
       representations are abelian (thompson-f-commutator-bound-holds-in-each-fixed-dimension).
  H4 : Higman's group <a1..a4 | a_{i+1}^-1 a_i a_{i+1} = a_i^2>, s = a_1.  No nontrivial finite
       quotients, so finite-dimensional unitary representations are trivial.  Soficity and
       hyperlinearity are OPEN (claim higman-group-is-sofic; Helfgott--Juschenko reduce it to
       base-two exponential permutations, open).  H4 is the "open, outside the permanence
       closure" control: a group with the same fd-rigidity as F and no known models.
  BG : Baumslag--Gersten <a,t | b^-1 a b = a^2, b = t^-1 a t>,  s = [a,t].  Every finite quotient
       is cyclic (Baumslag 1969), so every finite-dimensional unitary representation is abelian,
       and then a = a^2 forces a = I.  BG is an HNN extension of BS(1,2) over cyclic subgroups,
       hence sofic, hence hyperlinear: D_n(tau) -> 0 for BG (see bg_explicit.py for an explicit
       family with D_n = O(1/n^2)).

This is a heuristic float search (upper bounds on D_n(tau) only; nothing here bounds D_n below).
Usage: python3 defect_profile.py --group F --n 8 --tau 1.0 --restarts 8 --seed 1
"""

import argparse
import json
import math
import time

import torch

torch.set_default_dtype(torch.float64)
torch.set_num_threads(1)


def unitary(A):
    return torch.linalg.matrix_exp(A - A.conj().transpose(-2, -1))


def inv(X):
    return X.conj().transpose(-2, -1)


def e(X):
    n = X.shape[-1]
    return 2.0 - 2.0 * torch.real(torch.diagonal(X, dim1=-2, dim2=-1).sum(-1)) / n


def comm(X, Y):
    return X @ Y @ inv(X) @ inv(Y)


def words(group, mats):
    if group == "F":
        a, b = mats
        ai = inv(a)
        x = a @ inv(b)
        y = ai @ b @ a
        z = ai @ ai @ b @ a @ a
        return [comm(x, y), comm(x, z)], comm(a, b)
    if group == "BG":
        a, t = mats
        b = inv(t) @ a @ t
        return [inv(b) @ a @ b @ inv(a @ a)], comm(a, t)
    if group == "H4":
        # Higman's group: a_{i+1}^-1 a_i a_{i+1} = a_i^2 (indices mod 4); separating word s = a_1.
        rels = []
        for i in range(4):
            x, y = mats[i], mats[(i + 1) % 4]
            rels.append(inv(y) @ x @ y @ inv(x @ x))
        return rels, mats[0]
    raise ValueError(group)


NGEN = {"F": 2, "BG": 2, "H4": 4}
LR = 0.03


def seed_generators(path, n, noise, g):
    """Warm start: block-diagonal copies of a saved witness (dimension m | n), as A with exp(A - A^H) = U."""
    import numpy as np
    from scipy.linalg import schur

    W = np.load(path)
    m = W.shape[-1]
    assert n % m == 0, "witness dimension must divide n"
    out = []
    for U in W:
        T, Z = schur(U, output="complex")
        L = Z @ np.diag(1j * np.angle(np.diag(T))) @ Z.conj().T  # skew-Hermitian log of U
        L = np.kron(np.eye(n // m), L)
        A = torch.from_numpy(L / 2)
        A = A + noise * (torch.randn(n, n, generator=g) + 1j * torch.randn(n, n, generator=g))
        out.append(A.requires_grad_(True))
    return out


def run(group, n, tau, restarts, seed, steps, init=None, noise=0.05):
    g = torch.Generator().manual_seed(seed)
    ngen = NGEN[group]
    best = None
    for r in range(restarts):
        if init:
            A = seed_generators(init, n, noise, g)
        else:
            A = [
                (torch.randn(n, n, generator=g) + 1j * torch.randn(n, n, generator=g)).mul_(0.7).requires_grad_(True)
                for _ in range(ngen)
            ]
        opt = torch.optim.Adam(A, lr=LR)
        mu = 10.0
        rbest = None
        for it in range(steps):
            if it and it % (steps // 4) == 0:
                mu *= 10.0
            mats = [unitary(X) for X in A]
            rels, s = words(group, mats)
            ev = torch.stack([e(R) for R in rels])
            sep = e(s)
            soft = torch.logsumexp(40.0 * ev, 0) / 40.0
            loss = soft + mu * torch.relu(tau - sep) ** 2
            opt.zero_grad()
            loss.backward()
            opt.step()
            with torch.no_grad():
                m = float(ev.max())
                sv = float(sep)
                if sv >= tau and (rbest is None or m < rbest[0]):
                    rbest = (m, sv, it, [X.detach().clone() for X in mats])
        if rbest is not None and (best is None or rbest[0] < best[0]):
            best = rbest + (r,)
    return best


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--group", default="F")
    ap.add_argument("--n", type=int, default=4)
    ap.add_argument("--tau", type=float, default=1.0)
    ap.add_argument("--restarts", type=int, default=6)
    ap.add_argument("--steps", type=int, default=2000)
    ap.add_argument("--seed", type=int, default=20260917)
    ap.add_argument("--save", default=None, help="write the best witness (complex .npy stack) here")
    ap.add_argument("--init", default=None, help="warm start from a saved witness (dimension dividing n)")
    ap.add_argument("--noise", type=float, default=0.05)
    ap.add_argument("--lr", type=float, default=0.03)
    args = ap.parse_args()
    t0 = time.time()
    global LR
    LR = args.lr
    best = run(args.group, args.n, args.tau, args.restarts, args.seed, args.steps, args.init, args.noise)
    out = {
        "group": args.group, "n": args.n, "tau": args.tau, "restarts": args.restarts,
        "steps": args.steps, "seed": args.seed,
        "D_upper": None if best is None else best[0],
        "sep_at_best": None if best is None else best[1],
        "secs": round(time.time() - t0, 1),
    }
    if args.save and best is not None:
        import numpy as np
        np.save(args.save, torch.stack(best[3]).numpy())
        out["saved"] = args.save
    print(json.dumps(out))


if __name__ == "__main__":
    main()
