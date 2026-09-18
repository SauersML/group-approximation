#!/usr/bin/env python3
"""Operator-norm defect census for the two-generator Titz--Witzel group barGamma.

Presentation (TW2G2) of research/titz-witzel-sofic-gate-two-generators-four-
approximate-relators.md, generators e (=1), u (=2):
    e^2, c^2, rho^2 e^-1 u^-1, b x u^-1 d^-1, a c d b
with the words rebuilt from research/artifacts/titz-witzel-two-generator-free-
word-check.py.  u^8 is the separating word (lies in the simple index-2 residual K).

For each dimension k we search pairs (e,u) in U(k) with
  * e an EXACT involution  e = V diag(+1^p, -1^(k-p)) V^*,
  * u = diag(exp(i theta)) (conjugation fixes u diagonal), theta_0 = pi/8 fixed,
    so ||u^8 - 1||_op = 2 exactly (maximal separation),
minimising the maximum operator-norm relator defect
    delta(k) = min max_r || r(e,u) - 1 ||_op .
The objective is the smooth max  (1/2q) log sum_r tr(H_r^q),  H_r=(r-1)^*(r-1),
with q scheduled 1,4,16,64, Riemannian descent on U(k) x torus.

Every reported value is an UPPER bound for delta(k) witnessed by an explicit
double-precision tuple (e exact up to 1e-14).  A plateau is only heuristic
evidence against MF; decay would be heuristic evidence for MF.
"""
import sys, json, time
import numpy as np
from scipy.linalg import expm

# ---------- words -------------------------------------------------------------

def reduce_word(word, invols=(1,)):
    res = []
    for l in word:
        if abs(l) in invols:
            l = abs(l)
        if res and res[-1] == -l:
            res.pop()
        elif res and l in invols and res[-1] == l:
            res.pop()
        else:
            res.append(l)
    return tuple(res)

def P(*ws):
    return reduce_word([l for w in ws for l in w])

def I(w):
    return tuple(-l for l in reversed(w))

def Q(w, n):
    return P(*([w] * n)) if n >= 0 else Q(I(w), -n)

E, U = (1,), (2,)
h = P(U, E, I(U)); a = P(E, h, E); x = P(a, Q(U, 2)); c = P(Q(U, 2), a, Q(U, 2))
f = P(I(x), h, x); d = P(E, I(a), f); s = P(f, a, f)
rho = P(I(x), I(s), I(c)); b = P(rho, I(U), rho)
assert P(x, rho, c, s) == ()
RELATORS = {
    "c2": Q(c, 2),
    "r0": P(Q(rho, 2), I(E), I(U)),
    "r1": P(b, x, I(U), I(d)),
    "r2": P(a, c, d, b),
}

def exponent_sums(w):
    return sum(1 for l in w if l == 1), sum(1 if l == 2 else -1 if l == -2 else 0 for l in w)

WORDS = list(RELATORS.values())

def tokens(w):
    """Compress a word into tokens: 0 for e, nonzero n for u^n."""
    out = []
    for l in w:
        if l == 1:
            out.append(0)
        else:
            s = 1 if l == 2 else -1
            if out and out[-1] != 0:
                out[-1] += s
                if out[-1] == 0:
                    out.pop()
            else:
                out.append(s)
    return out

TOKS = [tokens(w) for w in WORDS]

# ---------- batched evaluation and gradient -----------------------------------
# Shapes: V (B,k,k) unitary, D (k,) signs, theta (B,k).  u = diag(exp(i theta)).

def H(M):
    return np.conj(np.swapaxes(M, -1, -2))

def build(V, D, theta):
    e = (V * D[None, None, :]) @ H(V)
    return 0.5 * (e + H(e)), np.exp(1j * theta)

def mul_tok(M, t, e, lam):
    return M @ e if t == 0 else M * (lam ** t)[:, None, :]

def objective(V, D, theta, q, want_grad=True):
    e, lam = build(V, D, theta)
    B, k = theta.shape
    Id = np.broadcast_to(np.eye(k, dtype=complex), (B, k, k))
    Gs, Rs, prefs = [], [], []
    for tk in TOKS:
        pref = [Id]
        for t in tk:
            pref.append(mul_tok(pref[-1], t, e, lam))
        Wm = pref[-1] - Id
        Hm = H(Wm) @ Wm
        Hq1 = np.linalg.matrix_power(Hm, q - 1) if q > 1 else Id
        Gs.append(np.real(np.einsum("bii->b", Hq1 @ Hm)))
        Rs.append(Wm @ Hq1)
        prefs.append(pref)
    S = sum(Gs)
    F = np.log(S) / (2 * q)
    if not want_grad:
        return F
    Ze = np.zeros((B, k, k), complex)
    gth = np.zeros((B, k))
    for tk, pref, R0 in zip(TOKS, prefs, Rs):
        T = R0
        for i in range(len(tk) - 1, -1, -1):
            t = tk[i]
            Ri = H(pref[i]) @ T
            if t == 0:
                Ze += Ri
                T = T @ e
            else:
                ln = lam ** t
                gth += np.real(np.conj(np.einsum("bii->bi", Ri)) * 1j * t * ln)
                T = T * np.conj(ln)[:, None, :]
    scale = (1.0 / S)[:, None]        # d/dX of (1/2q) log S with dS = 2q Re tr(R^* dX)
    gth *= scale
    Ze *= scale[:, :, None]
    gth[:, 0] = 0.0                   # frozen separating eigenvalue
    Zp = H(V) @ Ze @ V
    N = D[None, :, None] * H(Zp) - H(Zp) * D[None, None, :]
    GV = 0.5 * (H(N) - N)
    return F, GV, gth

def defects(V, D, theta):
    """Exact-ish (double precision) operator norms for a single tuple (B=1)."""
    e, lam = build(V, D, theta)
    e, lam = e[0], lam[0]
    k = e.shape[0]
    out = {}
    for name, tk in zip(RELATORS, TOKS):
        M = np.eye(k, dtype=complex)
        for t in tk:
            M = M @ e if t == 0 else M * (lam ** t)[None, :]
        out[name] = float(np.linalg.norm(M - np.eye(k), 2))
    out["e2"] = float(np.linalg.norm(e @ e - np.eye(k), 2))
    out["unit_e"] = float(np.linalg.norm(e @ e.conj().T - np.eye(k), 2))
    out["u8_sep"] = float(np.max(np.abs(lam ** 8 - 1)))
    return out

# ---------- batched Riemannian CG with per-sample Armijo ----------------------

def inner(GA, gA, GB, gB):
    return np.real(np.einsum("bij,bij->b", np.conj(GA), GB)) + np.einsum("bi,bi->b", gA, gB)

def cayley(A):
    """Exactly unitary Cayley retraction (I - A/2)^{-1} (I + A/2) of a skew batch A."""
    k = A.shape[-1]
    Id = np.eye(k)
    return np.linalg.solve(Id - 0.5 * A, Id + 0.5 * A)

def step(V, theta, dV, dth, t):
    return V @ cayley(-t[:, None, None] * dV), theta - t[:, None] * dth

def descend(V, D, theta, q, iters):
    B = V.shape[0]
    F, GV, gth = objective(V, D, theta, q)
    dV, dth = GV, gth
    g2 = inner(GV, gth, GV, gth)
    t = np.full(B, 0.05)
    active = np.ones(B, bool)
    for it in range(iters):
        slope = inner(GV, gth, dV, dth)
        bad = slope <= 0
        dV = np.where(bad[:, None, None], GV, dV)
        dth = np.where(bad[:, None], gth, dth)
        slope = np.where(bad, g2, slope)
        accepted = np.zeros(B, bool)
        V1, th1, F1 = V.copy(), theta.copy(), F.copy()
        for _ in range(12):
            Vt, tht = step(V, theta, dV, dth, t)
            Ft = objective(Vt, D, tht, q, want_grad=False)
            ok = active & (~accepted) & (Ft <= F - 1e-4 * t * slope)
            V1[ok], th1[ok], F1[ok] = Vt[ok], tht[ok], Ft[ok]
            accepted |= ok
            if (accepted | ~active).all():
                break
            t = np.where(accepted, t, 0.25 * t)
        active &= accepted | (t > 1e-9)
        if not active.any():
            break
        V, theta = V1, th1
        F, GV1, gth1 = objective(V, D, theta, q)
        beta = np.maximum(0.0, inner(GV1, gth1, GV1 - GV, gth1 - gth) / np.maximum(g2, 1e-300))
        beta = np.where(accepted, beta, 0.0)
        dV = GV1 + beta[:, None, None] * dV
        dth = gth1 + beta[:, None] * dth
        GV, gth, g2 = GV1, gth1, inner(GV1, gth1, GV1, gth1)
        t = np.where(accepted, np.minimum(3 * t, 1.0), t)
    return V, theta, F

def random_unitary(k, rng, B=1):
    Z = (rng.standard_normal((B, k, k)) + 1j * rng.standard_normal((B, k, k))) / np.sqrt(2)
    Qm, R = np.linalg.qr(Z)
    dg = np.einsum("bii->bi", R)
    return Qm * (dg / np.abs(dg))[:, None, :]

def optimise(V, D, theta, iters, qs=(1, 4, 16, 64)):
    for q in qs:
        V, theta, F = descend(V, D, theta, q, iters)
    return V, theta

def fd_check(k=5, seed=1):
    rng = np.random.default_rng(seed)
    D = np.array([1.0] * 2 + [-1.0] * (k - 2))
    V = random_unitary(k, rng, 2); theta = rng.uniform(-np.pi, np.pi, (2, k)); theta[:, 0] = np.pi / 8
    for q in (1, 3):
        F, GV, gth = objective(V, D, theta, q)
        Bm = rng.standard_normal((2, k, k)) + 1j * rng.standard_normal((2, k, k)); Bm = 0.5 * (Bm - H(Bm))
        dt = rng.standard_normal((2, k)); dt[:, 0] = 0
        eps = 1e-6
        Fp = objective(V @ expm(eps * Bm), D, theta + eps * dt, q, False)
        Fm = objective(V @ expm(-eps * Bm), D, theta - eps * dt, q, False)
        num = (Fp - Fm) / (2 * eps)
        ana = inner(GV, gth, Bm, dt)
        assert np.all(np.abs(num - ana) < 1e-6 * np.maximum(1, np.abs(num))), (q, num, ana)
    return True

def one_dim_baseline(theta0):
    best = np.inf
    for sgn in (1, -1):
        lam = np.exp(1j * theta0)
        best = min(best, max(abs(sgn ** exponent_sums(w)[0] * lam ** exponent_sums(w)[1] - 1) for w in WORDS))
    return best

# ---------- driver ------------------------------------------------------------

def best_of(V, D, theta):
    res = []
    for b in range(V.shape[0]):
        dfs = defects(V[b:b + 1], D, theta[b:b + 1])
        res.append((max(dfs[r] for r in RELATORS), b, dfs))
    return min(res, key=lambda z: z[0])

def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--ks", default="1,2,3,4,5,6,8,10,12,16,20,24,32")
    ap.add_argument("--t0", default="1.0,0.5,0.25")   # theta_0 = t0 * pi/8
    ap.add_argument("--batch", type=int, default=8)
    ap.add_argument("--iters", type=int, default=300)
    ap.add_argument("--seed", type=int, default=20260917)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    assert fd_check()
    print("finite-difference gradient check passed (batched, q=1,3)")
    for name, w in RELATORS.items():
        print(f"relator {name}: length {len(w)}, tokens {len(tokens(w))}, exponent sums (e,u) = {exponent_sums(w)}")
    rng = np.random.default_rng(args.seed)
    rows, witnesses = [], {}
    ks = [int(s) for s in args.ks.split(",")]
    for t0 in [float(s) for s in args.t0.split(",")]:
        theta0 = t0 * np.pi / 8
        sep = abs(np.exp(8j * theta0) - 1)
        base = one_dim_baseline(theta0)
        print(f"\n== theta0 = {t0}*pi/8, ||u^8-1||_op = {sep:.4f}, 1-dim baseline defect {base:.4f}", flush=True)
        prev = None
        for k in ks:
            t_start = time.time()
            cands = []
            # random starts over a few signatures
            for p in sorted(set([k // 2, (k + 1) // 2, k // 4, k - k // 4])):
                D = np.array([1.0] * p + [-1.0] * (k - p))
                V = random_unitary(k, rng, args.batch)
                th = rng.uniform(-np.pi, np.pi, (args.batch, k)); th[:, 0] = theta0
                V, th = optimise(V, D, th, args.iters)
                cands.append((best_of(V, D, th), V, D, th))
            # warm starts: previous witness (+) exact 1-dim reps (trivial, sign), perturbed
            if prev is not None:
                Vp, Dp, thp = prev
                m = k - Vp.shape[0]
                for blockD, blockth in ((1.0, 0.0), (-1.0, np.pi)):
                    D = np.concatenate([Dp, np.full(m, blockD)])
                    V0 = np.zeros((args.batch, k, k), complex)
                    V0[:, :Vp.shape[0], :Vp.shape[0]] = Vp
                    V0[:, Vp.shape[0]:, Vp.shape[0]:] = np.eye(m)
                    Bm = 0.05 * (rng.standard_normal((args.batch, k, k)) + 1j * rng.standard_normal((args.batch, k, k)))
                    Bm[0] = 0
                    V0 = V0 @ expm(0.5 * (Bm - H(Bm)))
                    th = np.concatenate([np.broadcast_to(thp, (args.batch, Vp.shape[0])),
                                         np.full((args.batch, m), blockth)], axis=1)
                    th = th + 0.05 * rng.standard_normal(th.shape); th[:, 0] = theta0
                    V0, th = optimise(V0, D, th, args.iters)
                    cands.append((best_of(V0, D, th), V0, D, th))
            (worst, b, dfs), V, D, th = min(cands, key=lambda z: z[0][0])
            prev = (V[b], D, th[b])
            witnesses[f"t{t0}_k{k}_V"] = V[b]; witnesses[f"t{t0}_k{k}_D"] = D; witnesses[f"t{t0}_k{k}_theta"] = th[b]
            rows.append(dict(t0=t0, sep=sep, k=k, delta_upper=worst, detail=dfs, baseline=base,
                             p=int((D > 0).sum()), secs=time.time() - t_start))
            print(f"k={k:3d}  delta(k) <= {worst:.5f}  p={int((D>0).sum())}  per-relator "
                  f"{[round(dfs[r], 4) for r in RELATORS]}  e2={dfs['e2']:.1e} sep={dfs['u8_sep']:.4f}"
                  f"  ({time.time()-t_start:.0f}s)", flush=True)
    if args.out:
        with open(args.out + ".json", "w") as fh:
            json.dump(rows, fh, indent=1)
        np.savez_compressed(args.out + "_witnesses.npz", **witnesses)

if __name__ == "__main__":
    main()
