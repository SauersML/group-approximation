"""Calibrate the normalized-HS probe of Thompson's V (hs_probe.py) on presentations with known answers.

Run on MSI only.  Same parametrization and optimizer as hs_probe.py:
u = W_u D6 W_u^*, v = W_v D3 W_v^* with balanced 6th and 3rd root spectra (u^6 = v^3 = 1
exact, u^3 at energy 2), Riemannian gradient descent on the mean squared normalized HS
defect of the remaining relators.  Three relator sets are compared at each dimension d:

  V        the five Bleak--Quick relators of V (lengths 16, 69, 31, 25, 35); no finite
           exact models exist since V is simple, so the answer is unknown.
  planted  the same five words raised to the power m_i = order of r_i(x, y) in S_5, where
           x has cycle type (2)(3) and y is a 3-cycle generating S_5 together with x.
           The 6-dimensional irreducible representation of S_5 gives balanced spectra
           for x and y, so an EXACT solution exists at every d = 6k.  Success here means
           the optimizer can find exact far-from-trivial solutions of long relators.
  null     random words of the same lengths as the V relators.  Such presentations are
           almost surely trivial or finite with no balanced-spectrum models, so their
           plateau is the generic floor of the landscape.

The planted words are longer than V's (m_i up to 6), so success on them is a conservative
calibration; failure would make the V plateau uninformative.

Usage: python3 calibrate_hs.py --sets planted null V --dims 6 12 24 --seeds 3 --iters 1500 --out FILE.json
"""
import argparse
import itertools
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
V_RELATORS = [texwords.parse(r) for r in P["relators_tex"][2:]]


def perm_matrix(p):
    n = len(p)
    m = np.zeros((n, n), dtype=np.int64)
    for j in range(n):
        m[p[j], j] = 1
    return m


def word_perm(word, M):
    out = np.eye(M["u"].shape[0], dtype=np.int64)
    for x, e in word:
        out = out @ (M[x] if e > 0 else M[x].T)
    return out


def order_of(A):
    B = A.copy()
    I = np.eye(A.shape[0], dtype=np.int64)
    for k in range(1, 121):
        if np.array_equal(B, I):
            return k
        B = B @ A
    raise ValueError("order > 120")


def group_order(gens):
    I = tuple(range(5))
    seen = {I}
    frontier = [I]
    while frontier:
        nxt = []
        for g in frontier:
            for s in gens:
                h = tuple(s[g[i]] for i in range(5))
                if h not in seen:
                    seen.add(h)
                    nxt.append(h)
        frontier = nxt
    return len(seen)


def planted_s5_relators(seed):
    rng = np.random.default_rng(1000 + seed)
    while True:
        a = rng.permutation(5)
        b = rng.permutation(5)
        x = np.arange(5)
        x[a[0]], x[a[1]] = a[1], a[0]
        x[a[2]], x[a[3]], x[a[4]] = a[3], a[4], a[2]
        y = np.arange(5)
        y[b[0]], y[b[1]], y[b[2]] = b[1], b[2], b[0]
        if group_order([tuple(x), tuple(y)]) == 120:
            break
    M = {"u": perm_matrix(x), "v": perm_matrix(y)}
    assert order_of(M["u"]) == 6 and order_of(M["v"]) == 3
    rels, ms = [], []
    for r in V_RELATORS:
        m = order_of(word_perm(r, M))
        ms.append(m)
        rels.append(r * m)
    for r in rels:
        assert np.array_equal(word_perm(r, M), np.eye(5, dtype=np.int64))
    return rels, ms


def null_relators(seed):
    rng = np.random.default_rng(2000 + seed)
    letters = [("u", 1), ("u", -1), ("v", 1), ("v", -1)]
    rels = []
    for r in V_RELATORS:
        w = []
        while len(w) < len(r):
            c = letters[rng.integers(4)]
            if w and w[-1][0] == c[0] and w[-1][1] == -c[1]:
                continue
            w.append(c)
        rels.append(w)
    return rels


def haar(d, rng):
    z = (rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))) / np.sqrt(2)
    q, r = np.linalg.qr(z)
    return q * (np.diag(r) / np.abs(np.diag(r)))


def roots_diag(d, k):
    return np.exp(2j * np.pi * (np.arange(d) % k) / k)


def loss_and_grads(U, d, rels):
    G = {"u": np.zeros((d, d), dtype=complex), "v": np.zeros((d, d), dtype=complex)}
    defs = []
    for word in rels:
        fs = [U[x] if e > 0 else U[x].conj().T for x, e in word]
        m = len(fs)
        pre = [np.eye(d, dtype=complex)]
        for f in fs:
            pre.append(pre[-1] @ f)
        suf = [None] * (m + 1)
        suf[m] = np.eye(d, dtype=complex)
        for j in range(m - 1, -1, -1):
            suf[j] = fs[j] @ suf[j + 1]
        defs.append(float(2 - 2 * np.real(np.trace(pre[m])) / d))
        for j, (x, e) in enumerate(word):
            Mj = suf[j + 1] @ pre[j]
            G[x] += -(2.0 / d) * (Mj.conj().T if e > 0 else Mj) / len(rels)
    return float(np.mean(defs)), defs, G


def run(d, seed, iters, lr0, rels):
    rng = np.random.default_rng(seed)
    D = {"u": roots_diag(d, 6), "v": roots_diag(d, 3)}
    W = {"u": haar(d, rng), "v": haar(d, rng)}

    def build(W):
        return {x: (W[x] * D[x]) @ W[x].conj().T for x in "uv"}

    U = build(W)
    L, defs, G = loss_and_grads(U, d, rels)
    L0, lr, t0, it = L, lr0, time.time(), 0
    for it in range(iters):
        newW = {}
        for x in "uv":
            H = W[x].conj().T @ G[x] @ W[x]
            M = D[x][:, None] * H.conj().T - H.conj().T * D[x][None, :]
            Ms = M.conj().T
            newW[x] = W[x] @ expm(lr * (-(Ms - Ms.conj().T) / 2))
        newU = build(newW)
        nL, ndefs, nG = loss_and_grads(newU, d, rels)
        if nL < L:
            W, U, L, defs, G = newW, newU, nL, ndefs, nG
            lr = min(lr * 1.2, 50.0)
        else:
            lr *= 0.5
            if lr < 1e-9:
                break
        if L < 1e-10:
            break
    return {"d": d, "seed": seed, "iters_done": it + 1, "initial_mean_sq_defect": L0,
            "final_mean_sq_defect": L, "final_max_hs_defect": float(np.sqrt(max(defs))),
            "per_relator_sq_defect": defs, "seconds": time.time() - t0}


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--sets", nargs="+", default=["planted", "null", "V"])
    ap.add_argument("--dims", type=int, nargs="+", default=[6, 12, 24])
    ap.add_argument("--seeds", type=int, default=3)
    ap.add_argument("--iters", type=int, default=1500)
    ap.add_argument("--lr", type=float, default=0.5)
    ap.add_argument("--out", default="calibrate_hs_results.json")
    a = ap.parse_args()
    results = []
    for name, d, s in itertools.product(a.sets, a.dims, range(a.seeds)):
        assert d % 6 == 0
        info = {}
        if name == "V":
            rels = V_RELATORS
        elif name == "planted":
            rels, ms = planted_s5_relators(s)
            info["planted_powers"] = ms
        elif name == "null":
            rels = null_relators(s)
        else:
            raise ValueError(name)
        info["relator_lengths"] = [len(r) for r in rels]
        r = run(d, s, a.iters, a.lr, rels)
        r.update({"set": name, **info})
        results.append(r)
        print(json.dumps({k: r[k] for k in ("set", "d", "seed", "iters_done", "final_mean_sq_defect",
                                            "final_max_hs_defect", "relator_lengths", "seconds")}
                         | ({"planted_powers": info["planted_powers"]} if "planted_powers" in info else {})),
              flush=True)
        json.dump(results, open(a.out, "w"), indent=1)
