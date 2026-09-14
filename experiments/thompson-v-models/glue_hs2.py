"""Calibrated unitary free gluings for Thompson's V: annealed and restarted descent against S5 controls.

Run on MSI only (module load python/3.10.10-gcc-8.2.0-sanagub; OMP_NUM_THREADS=1).
Extends glue_hs.py (same standard form, loss and exact commutant gradient; imported, not copied).

Word sets (all of the lengths of r5..r8 or longer):
  V      r5..r8 of Bleak--Quick (2.4), rel_V.txt.
  CTRL   rel_CTRL.txt: four reduced words of the lengths of r5..r8 that are trivial in S5 under
         a = (0 1), b = (1 2 3), c = (0 4) (gen_ctrl.py).  The left regular representation of S5 gives
         an exact free gluing at every N divisible by 120; this script builds it and checks exactness,
         trying both word conventions and refusing to run CTRL if neither is exact.
  PLANT  the V words raised to their orders in S5 (glue_hs.planted), exact at N divisible by 120.

Methods:
  descent   glue_hs.run's adaptive Riemannian descent from a Haar start in the commutant of A.
  anneal    the same descent interleaved with random commutant rotations exp(sigma Om), accepted by a
            Metropolis rule at temperature T; sigma and T decrease geometrically; final polish.
  restart   R short descents from independent Haar starts, then a long polish of the best.

Usage: python3 glue_hs2.py --task "MODE N SEED METHOD" --iters 3000 --out F.json
"""
import argparse, json, os, sys, time
import numpy as np
from scipy.linalg import expm

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import glue_hs as g
import texwords

S5 = "1,0,2,3,4;0,2,3,1,4;4,1,2,3,0"


def rel(name):
    return [texwords.parse(l.strip()) for l in open(os.path.join(HERE, name)) if l.strip()]


def reverse(w):
    return list(reversed(w))


def ctrl2_exact_gluing(A, B, N):
    """PSL(2,17) control (gen_ctrl2.log): <a,b,c> of order 2448 acts on the 144 cosets of an element of
    order 17, freely for <a,b> and <a,c>.  Returns C (standard form, N/144 copies) or raises."""
    lines = open(os.path.join(HERE, "gen_ctrl2.log")).read().splitlines()
    gens = {l[0]: tuple(int(x) for x in l.split("=", 1)[1].strip(" ()").split(",")) for l in lines[:3]}
    mul = lambda s, t: tuple(t[s[i]] for i in range(18))  # first s then t
    e = tuple(range(18))
    G, fr = {e}, [e]
    while fr:
        nf = []
        for p in fr:
            for s in gens.values():
                q = mul(p, s)
                if q not in G:
                    G.add(q)
                    nf.append(q)
        fr = nf
    assert len(G) == 2448
    x17 = next(p for p in G if p != e and mul(mul(p, p), p) != e and all(
        pow_ok for pow_ok in [len({tuple(p)} | set()) > 0]) and order18(p, mul) == 17)
    H, y = [e], x17
    while y != e:
        H.append(y)
        y = mul(y, x17)
    cos, index = {}, []
    for gg in G:
        c = frozenset(mul(h, gg) for h in H)
        if c not in cos:
            cos[c] = len(index)
            index.append(c)
    assert len(index) == 144
    rep = [next(iter(c)) for c in index]
    act = {l: np.array([cos[frozenset(mul(h, mul(rep[i], s)) for h in H)] for i in range(144)]) for l, s in gens.items()}
    k = N // 24
    phi, base, blk = -np.ones(N, dtype=int), 0, 0
    Cfull = np.zeros(N, dtype=int)
    for copy in range(N // 144):
        seen = -np.ones(144, dtype=int)
        for start in range(144):
            if seen[start] >= 0:
                continue
            seen[start], frontier = 24 * blk, [start]
            while frontier:
                nxt = []
                for p in frontier:
                    for l, arr in (("a", A), ("b", B)):
                        for q, img in ((act[l][p], arr[seen[p]]), (int(np.argsort(act[l])[p]), int(np.argsort(arr)[seen[p]]))):
                            if seen[q] < 0:
                                seen[q] = img
                                nxt.append(q)
                            else:
                                assert seen[q] == img, "orbit relabeling inconsistent"
                frontier = nxt
            blk += 1
        for p in range(144):
            Cfull[seen[p] + 0] = seen[act["c"][p]]
    assert blk == k
    return Cfull


def order18(p, mul):
    e, x, n = tuple(range(18)), p, 1
    while x != e:
        x, n = mul(x, p), n + 1
    return n


def setup(mode, N):
    k = N // 24
    A, B, C0 = g.standard(k)
    perms = {"a": A, "b": B}
    info = {}
    if mode == "V":
        return A, B, C0, perms, g.V_WORDS, info
    if mode == "CTRL2":
        assert N % 144 == 0, "CTRL2 needs N divisible by 144"
        Cx, I = ctrl2_exact_gluing(A, B, N), np.eye(N)
        Cd = g.dense(Cx)
        assert np.allclose(Cd @ Cd, I) and np.allclose(np.linalg.matrix_power(g.dense(A) @ Cd, 3), I)
        ctrl = rel("rel_CTRL2.txt")

        def exact2(words):
            return max(float(np.linalg.norm(g.word_value(g.syllables(w, perms), Cd) - I) / np.sqrt(N)) for w in words)

        e_fwd, e_rev = exact2(ctrl), exact2([reverse(w) for w in ctrl])
        info = dict(Q_order=2448, ctrl2_exact_forward=e_fwd, ctrl2_exact_reversed=e_rev)
        if e_fwd < 1e-9:
            return A, B, C0, perms, ctrl, dict(info, convention="forward")
        if e_rev < 1e-9:
            return A, B, C0, perms, [reverse(w) for w in ctrl], dict(info, convention="reversed")
        raise SystemExit("CTRL2 words are not exact in either convention: %r" % info)
    powered, ords, Cp, qn = g.planted(S5, k, A, B)
    Cd, I = g.dense(Cp), np.eye(N)

    def exact(words):
        return max(float(np.linalg.norm(g.word_value(g.syllables(w, perms), Cd) - I) / np.sqrt(N)) for w in words)

    if mode == "PLANT":
        info = dict(Q_order=qn, powers=ords, planted_exact_max_hs=exact(powered))
        return A, B, C0, perms, powered, info
    ctrl = rel("rel_CTRL.txt")
    e_fwd, e_rev = exact(ctrl), exact([reverse(w) for w in ctrl])
    info = dict(Q_order=qn, ctrl_exact_forward=e_fwd, ctrl_exact_reversed=e_rev)
    if e_fwd < 1e-9:
        return A, B, C0, perms, ctrl, dict(info, convention="forward")
    if e_rev < 1e-9:
        return A, B, C0, perms, [reverse(w) for w in ctrl], dict(info, convention="reversed")
    raise SystemExit("CTRL words are not exact in either convention: %r" % info)


def descend(syls, C, A, iters, lr=0.5):
    L, defs, S = g.loss_grad(syls, C, A)
    for it in range(iters):
        E = expm(lr * S)
        nC = E @ C @ E.conj().T
        nL, nd, nS = g.loss_grad(syls, nC, A)
        if nL < L:
            C, L, defs, S, lr = nC, nL, nd, nS, min(lr * 1.2, 50.0)
        else:
            lr *= 0.5
            if lr < 1e-10:
                break
    return C, L, defs


def haar_start(C0d, A, rng):
    W = g.random_commutant_unitary(A, rng)
    return W.conj().T @ C0d @ W


def run(mode, N, seed, method, iters):
    rng = np.random.default_rng(seed)
    A, B, C0, perms, words, info = setup(mode, N)
    syls = [g.syllables(w, perms) for w in words]
    C0d, t0, hist = g.dense(C0), time.time(), []
    if method == "descent":
        C, L, defs = descend(syls, haar_start(C0d, A, rng), A, iters)
    elif method == "restart":
        best = None
        for r in range(40):
            C, L, defs = descend(syls, haar_start(C0d, A, rng), A, 150)
            hist.append((r, L))
            if best is None or L < best[1]:
                best = (C, L, defs)
        C, L, defs = descend(syls, best[0], A, iters)
    elif method == "anneal":
        C, L, defs = descend(syls, haar_start(C0d, A, rng), A, 100)
        best, T0, T1, s0, s1 = (C, L, defs), 0.05, 1e-4, 0.3, 0.01
        for it in range(iters):
            f = it / max(iters - 1, 1)
            T, sigma = T0 * (T1 / T0) ** f, s0 * (s1 / s0) ** f
            Om = g.random_commutant_skew(A, rng)
            E = expm(sigma * Om)
            nC, nL, nd = descend(syls, E @ C @ E.conj().T, A, 5)
            if nL < L or rng.random() < np.exp(-(nL - L) / T):
                C, L, defs = nC, nL, nd
                if L < best[1]:
                    best = (C, L, defs)
            if it % 100 == 0:
                hist.append((it, float(L), float(best[1])))
            if best[1] < 1e-8:
                break
        C, L, defs = descend(syls, best[0], A, 1500)
    else:
        raise SystemExit("unknown method " + method)
    I = np.eye(N)
    return dict(mode=mode, N=N, seed=seed, method=method, iters=iters, final_mean_sq=float(L),
                final_max_hs=float(np.sqrt(max(max(defs), 0.0))), per_word_sq=[float(x) for x in defs],
                word_lengths=[len(w) for w in words], seconds=time.time() - t0,
                s3_relation_residual=float(max(np.linalg.norm(C @ C - I),
                                               np.linalg.norm(np.linalg.matrix_power(g.dense(A) @ C, 3) - I)) / np.sqrt(N)),
                history=hist, **info)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--task", required=True)
    ap.add_argument("--iters", type=int, default=3000)
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    mode, N, seed, method = a.task.split()[:4]
    r = run(mode, int(N), int(seed), method, a.iters)
    print(json.dumps({k: v for k, v in r.items() if k != "history"}), flush=True)
    json.dump(r, open(a.out, "w"), indent=1)
