#!/usr/bin/env python3
"""Multi-separation HS census for Thompson's F.

    D_n(tau; S) = inf { max_i e(R_i(U)) : U in U(n)^2, e(w(U)) >= tau for every w in S },
    e(X) = ||X - I||_2^2 = 2 - 2 Re tr_n X.

S = S_L is a set of representatives of the cyclic classes of nontrivial elements of F' of length
<= L (all nontrivial: F has no relation of length < 10; checked in trace_test.py).  For S = {c}
this is the w19 census D_n(tau).  If F is hyperlinear then D_n(tau; S) -> 0 for every finite S of
nontrivial elements and every tau < 2 (tensor-power amplification of a regular-type witness), so
each S gives an equivalent census; a larger S only rules out witnesses that separate c "cheaply"
while collapsing other nontrivial elements of F'.

Usage: python3 constrained_census.py --n 16 --L 6 --tau 1.8 --restarts 4 --steps 2000
"""

import argparse
import itertools
import json
import time

import numpy as np
import torch

torch.set_default_dtype(torch.float64)
torch.set_num_threads(1)

INV = {"a": "A", "A": "a", "b": "B", "B": "b"}


def classes(L):
    out = set()
    for k in range(4, L + 1, 2):
        for t in itertools.product("aAbB", repeat=k):
            w = "".join(t)
            if any(w[i + 1] == INV[w[i]] for i in range(k - 1)) or w[-1] == INV[w[0]]:
                continue
            if w.count("a") != w.count("A") or w.count("b") != w.count("B"):
                continue
            rots = [w[i:] + w[:i] for i in range(k)]
            wi = "".join(INV[x] for x in reversed(w))
            rots += [wi[i:] + wi[:i] for i in range(k)]
            out.add(min(rots))
    # keep c = [a,b] first
    out = sorted(out, key=lambda s: (len(s), s))
    return out


def unitary(A):
    return torch.linalg.matrix_exp(A - A.conj().transpose(-2, -1))


def e(X):
    n = X.shape[-1]
    return 2.0 - 2.0 * torch.real(torch.diagonal(X).sum()) / n


def word(w, M):
    X = None
    for x in w:
        X = M[x] if X is None else X @ M[x]
    return X


R1 = "aB" + "Aba" + "bA" + "ABa"
R2 = "aB" + "AAbaa" + "bA" + "AABaa"


def seed(path, n, noise, g):
    from scipy.linalg import schur
    W = np.load(path)
    m = W.shape[-1]
    assert n % m == 0
    out = []
    for U in W:
        T, Z = schur(U, output="complex")
        Lg = Z @ np.diag(1j * np.angle(np.diag(T))) @ Z.conj().T
        Lg = np.kron(np.eye(n // m), Lg)
        A = torch.from_numpy(Lg / 2) + noise * (torch.randn(n, n, generator=g) + 1j * torch.randn(n, n, generator=g))
        out.append(A.requires_grad_(True))
    return out


def run(n, S, tau, restarts, steps, sd, lr, init, noise):
    g = torch.Generator().manual_seed(sd)
    best = None
    for r in range(restarts):
        if init:
            A = seed(init, n, noise, g)
        else:
            A = [(torch.randn(n, n, generator=g) + 1j * torch.randn(n, n, generator=g)).mul_(0.7).requires_grad_(True)
                 for _ in range(2)]
        opt = torch.optim.Adam(A, lr=lr)
        mu = 10.0
        for it in range(steps):
            if it and it % (steps // 4) == 0:
                mu *= 10.0
            a, b = unitary(A[0]), unitary(A[1])
            M = {"a": a, "A": a.conj().T, "b": b, "B": b.conj().T}
            ev = torch.stack([e(word(R1, M)), e(word(R2, M))])
            sep = torch.stack([e(word(w, M)) for w in S])
            loss = torch.logsumexp(40.0 * ev, 0) / 40.0 + mu * (torch.relu(tau - sep) ** 2).sum()
            opt.zero_grad()
            loss.backward()
            opt.step()
            with torch.no_grad():
                m, s = float(ev.max()), float(sep.min())
                if s >= tau and (best is None or m < best[0]):
                    best = (m, [float(x) for x in sep], r, it, torch.stack([a, b]).detach().clone())
    return best


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=8)
    ap.add_argument("--L", type=int, default=6, help="S = F' classes of length <= L; L=4 means S={c}")
    ap.add_argument("--tau", type=float, default=1.8)
    ap.add_argument("--restarts", type=int, default=4)
    ap.add_argument("--steps", type=int, default=2000)
    ap.add_argument("--seed", type=int, default=917)
    ap.add_argument("--lr", type=float, default=0.03)
    ap.add_argument("--init", default=None)
    ap.add_argument("--noise", type=float, default=0.05)
    ap.add_argument("--save", default=None)
    args = ap.parse_args()
    S = classes(args.L)
    t0 = time.time()
    best = run(args.n, S, args.tau, args.restarts, args.steps, args.seed, args.lr, args.init, args.noise)
    out = {"n": args.n, "L": args.L, "|S|": len(S), "tau": args.tau, "restarts": args.restarts,
           "steps": args.steps, "seed": args.seed, "init": args.init,
           "D_upper": None if best is None else best[0],
           "ratio_sq_lower": None if best is None else args.tau / best[0],
           "sep_min": None if best is None else min(best[1]), "secs": round(time.time() - t0, 1)}
    if args.save and best is not None:
        np.save(args.save, best[4].numpy())
        out["saved"] = args.save
    print(json.dumps(out), flush=True)


if __name__ == "__main__":
    main()
