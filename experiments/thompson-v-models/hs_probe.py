"""Normalized Hilbert--Schmidt almost-representations of Thompson's V: a numerical probe.

Run on MSI only.  Presentation: Bleak--Quick two generators u, v and seven
relators (presentation_bq2.json, verified exactly by verify_bq2.py).

Parametrization.  u = W_u D6 W_u^*, v = W_v D3 W_v^*, where D6 (D3) carries the
6th (3rd) roots of unity with equal multiplicity.  Relators u^6 and v^3 then hold
exactly, and every power u^k (k=1..5), v^(+-1) is traceless, i.e. has squared
normalized HS energy exactly 2 (the regular value).  In particular a = u^3 =
t_(00,01) sits at energy 2 by construction, so a small defect on the remaining
five relators is a model of V that is far from trivial on the marked word.

Loss: mean over relators r of ||r(U) - I||_2^2 = 2 - 2 Re tr(r(U))/d, with the
normalized trace.  Riemannian gradient descent on W_u, W_v in U(d) with
exact gradients.  Reports, per run, the mean and max normalized HS relator
defect and the energies of a few test words that are not powers of generators.

Usage: python3 hs_probe.py --dims 6 12 24 48 --seeds 4 --iters 1500 --out FILE.json
"""
import argparse
import json
import os
import sys
import time

import numpy as np
from scipy.linalg import expm

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import texwords

HERE = os.path.dirname(os.path.abspath(__file__))
P = json.load(open(os.path.join(HERE, "presentation_bq2.json")))
RELATORS = [texwords.parse(r) for r in P["relators_tex"][2:]]  # u^6, v^3 exact
TEST_WORDS = {
    "[u,v]": texwords.parse("u^{-1}v^{-1}uv"),
    "uv": texwords.parse("uv"),
    "u^3 v": texwords.parse("u^{3}v"),
    "t_(11,001)": texwords.conj(texwords.parse("u^{3}"), texwords.parse("vu^{-1}vu^{3}v")),
}


def haar(d, rng):
    z = (rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))) / np.sqrt(2)
    q, r = np.linalg.qr(z)
    ph = np.diag(r) / np.abs(np.diag(r))
    return q * ph


def roots_diag(d, k):
    return np.exp(2j * np.pi * (np.arange(d) % k) / k)


def factors(word, U):
    out = []
    for x, e in word:
        out.append(U[x] if e > 0 else U[x].conj().T)
    return out


def word_matrix(word, U, d):
    m = np.eye(d, dtype=complex)
    for f in factors(word, U):
        m = m @ f
    return m


def energy(word, U, d):
    return float(2 - 2 * np.real(np.trace(word_matrix(word, U, d))) / d)


def loss_and_grads(U, d):
    """Return mean squared defect, per-relator defects, Euclidean grads wrt U['u'], U['v']."""
    G = {"u": np.zeros((d, d), dtype=complex), "v": np.zeros((d, d), dtype=complex)}
    defs = []
    for word in RELATORS:
        fs = factors(word, U)
        m = len(fs)
        pre = [np.eye(d, dtype=complex)]
        for f in fs:
            pre.append(pre[-1] @ f)
        suf = [np.eye(d, dtype=complex)] * (m + 1)
        for j in range(m - 1, -1, -1):
            suf[j] = fs[j] @ suf[j + 1]
        tr = np.trace(pre[m])
        defs.append(float(2 - 2 * np.real(tr) / d))
        for j, (x, e) in enumerate(word):
            M = suf[j + 1] @ pre[j]
            g = M.conj().T if e > 0 else M
            G[x] += -(2.0 / d) * g / len(RELATORS)
    return float(np.mean(defs)), defs, G


def run(d, seed, iters, lr0):
    assert d % 6 == 0
    rng = np.random.default_rng(seed)
    D = {"u": roots_diag(d, 6), "v": roots_diag(d, 3)}
    W = {"u": haar(d, rng), "v": haar(d, rng)}

    def build(W):
        return {x: (W[x] * D[x]) @ W[x].conj().T for x in "uv"}

    U = build(W)
    L, defs, G = loss_and_grads(U, d)
    L0 = L
    lr = lr0
    t0 = time.time()
    for it in range(iters):
        newW = {}
        for x in "uv":
            H = W[x].conj().T @ G[x] @ W[x]
            Dm = D[x][:, None]
            M = Dm * H.conj().T - H.conj().T * D[x][None, :]
            Ms = M.conj().T
            omega = -(Ms - Ms.conj().T) / 2
            newW[x] = W[x] @ expm(lr * omega)
        newU = build(newW)
        nL, ndefs, nG = loss_and_grads(newU, d)
        if nL < L:
            W, U, L, defs, G = newW, newU, nL, ndefs, nG
            lr = min(lr * 1.2, 50.0)
        else:
            lr *= 0.5
            if lr < 1e-9:
                break
    return {
        "d": d,
        "seed": seed,
        "iters_done": it + 1,
        "initial_mean_sq_defect": L0,
        "final_mean_sq_defect": L,
        "final_max_hs_defect": float(np.sqrt(max(defs))),
        "per_relator_sq_defect": defs,
        "test_word_energies": {k: energy(w, U, d) for k, w in TEST_WORDS.items()},
        "seconds": time.time() - t0,
    }


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--dims", type=int, nargs="+", default=[6, 12, 24, 48])
    ap.add_argument("--seeds", type=int, default=4)
    ap.add_argument("--iters", type=int, default=1500)
    ap.add_argument("--lr", type=float, default=0.5)
    ap.add_argument("--out", default="hs_probe_results.json")
    a = ap.parse_args()
    results = []
    for d in a.dims:
        for s in range(a.seeds):
            r = run(d, s, a.iters, a.lr)
            results.append(r)
            print(json.dumps({k: r[k] for k in ("d", "seed", "iters_done", "final_mean_sq_defect",
                                                "final_max_hs_defect", "test_word_energies", "seconds")}),
                  flush=True)
            json.dump(results, open(a.out, "w"), indent=1)
