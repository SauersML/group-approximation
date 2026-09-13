"""Unitary free gluings for Thompson's V: a normalized-HS descent with planted controls.

Run on MSI only (module load python/3.10.10-gcc-8.2.0-sanagub; OMP_NUM_THREADS=1).

A unitary free gluing of size N = 24k (claim thompson-v-hyperlinear-iff-unitary-s4-s3-gluings-fix-long-words):
A, B are the permutation matrices of left multiplication by a, b on the free S4-set S4 x [k], C0 is a
fixed free S3-structure on the same set in which a acts as A, and C = W^* C0 W for a unitary W commuting
with A.  So (A, B) is k copies of the regular representation of S4, (A, C) is 4k copies of the regular
representation of S3, and every short relator holds exactly.  Loss: mean over the long words r of
||r(A,B,C) - I||_2^2 = 2 - 2 Re tr_N r (normalized trace).  Riemannian descent C <- e^{-Om} C e^{Om},
Om skew-Hermitian in the commutant of A, exact gradient, adaptive step.

Word sets
  V        r5..r8 of Bleak--Quick (2.4), rel_V.txt.
  planted  the same words raised to their orders in a finite group Q = <a,b,c> in which <a,b> = S4 and
           <a,c> = S3.  The left regular representation of Q is an exact gluing, so exact solutions
           exist at every N divisible by |Q|.
  null     random words over a, b^(+-1), c with the letter counts of r5..r8.

Usage:
  python3 glue_hs.py --task "MODE N SEED [Q=a;b;c] [basin=EPS]" --iters 3000 --out F.json
  python3 glue_hs.py --fdcheck --out F.json        (gradient versus finite differences)
  python3 glue_hs.py --findq 7 --out F.json         (control groups inside Sym(n))
"""
import argparse, itertools, json, os, sys, time
import numpy as np
from scipy.linalg import expm

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import texwords

V_WORDS = [texwords.parse(l.strip()) for l in open(os.path.join(HERE, "rel_V.txt")) if l.strip()]
S4A, S4B = (1, 0, 2, 3), (0, 2, 3, 1)
S3A, S3C = (1, 0, 2), (0, 2, 1)


def comp(p, q):  # (p o q)(x) = p(q(x)); left regular matrices then satisfy L(p)L(q) = L(p o q)
    return tuple(p[i] for i in q)


def inv(p):
    out = [0] * len(p)
    for i, j in enumerate(p):
        out[j] = i
    return tuple(out)


def closure(gens):
    e = tuple(range(len(gens[0])))
    seen, frontier = {e: None}, [e]
    while frontier:
        nxt = []
        for h in frontier:
            for g in gens:
                x = comp(g, h)
                if x not in seen:
                    seen[x] = None
                    nxt.append(x)
        frontier = nxt
    return list(seen)


def word_elem(word, G):
    x = tuple(range(len(G["a"])))
    for l, e in word:
        x = comp(x, G[l] if e > 0 else inv(G[l]))
    return x


def order(p):
    e, x, n = tuple(range(len(p))), p, 1
    while x != e:
        x, n = comp(x, p), n + 1
    return n


def left_regular(elems, g):
    idx = {h: i for i, h in enumerate(elems)}
    return np.array([idx[comp(g, h)] for h in elems])


def standard(k):
    """Permutation arrays A, B, C0 on N = 24k points: free S4-set glued to a free S3-set along a."""
    s4, s3 = closure([S4A, S4B]), closure([S3A, S3C])
    A4, B4 = left_regular(s4, S4A), left_regular(s4, S4B)
    A3, C3 = left_regular(s3, S3A), left_regular(s3, S3C)
    A = np.concatenate([A4 + 24 * j for j in range(k)])
    B = np.concatenate([B4 + 24 * j for j in range(k)])
    pairs = [(h + 24 * j, A4[h] + 24 * j) for j in range(k) for h in range(24) if h < A4[h]]
    reps3 = [g for g in range(6) if g < A3[g]]
    phi = {}
    for t, (h, ah) in enumerate(pairs):
        r, jj = reps3[t % 3], t // 3
        phi[(r, jj)], phi[(A3[r], jj)] = h, ah
    C0 = np.zeros(24 * k, dtype=int)
    for (g, jj), y in phi.items():
        C0[y] = phi[(C3[g], jj)]
    return A, B, C0


def dense(p):
    M = np.zeros((len(p), len(p)), dtype=complex)
    M[p, np.arange(len(p))] = 1.0
    return M


def syllables(word, perms):
    """P_pi0 C P_pi1 C ... C P_pit; c is an involution, so c^-1 = c."""
    cur, out = np.arange(len(perms["a"])), []
    for l, e in word:
        if l == "c":
            out.append(cur)
            cur = np.arange(len(perms["a"]))
        else:
            cur = cur[perms[l] if e > 0 else np.argsort(perms[l])]  # P_cur P_p = P_(cur o p)
    out.append(cur)
    return out


def word_value(syl, C):
    M = dense(syl[0])
    for p in syl[1:]:
        M = (M @ C)[:, p]  # M P_p = M[:, p]
    return M


def loss_grad(syls, C, A):
    N = C.shape[0]
    defs, G = [], np.zeros_like(C)
    for syl in syls:
        t = len(syl) - 1
        pre, M = [], dense(syl[0])
        for j in range(t):
            pre.append(M)
            M = (M @ C)[:, syl[j + 1]]
        defs.append(float(2 - 2 * np.real(np.trace(M)) / N))
        post, S = [None] * t, dense(syl[t])
        for j in range(t - 1, -1, -1):
            post[j] = S
            if j > 0:
                S = (C @ S)[np.argsort(syl[j]), :]  # P_p M = M[p^-1, :]
        X = sum(post[j] @ pre[j] for j in range(t))
        G += (X @ C - C @ X) * (2.0 / N)
    G /= len(syls)
    Sk = (G - G.conj().T) / 2
    return float(np.mean(defs)), defs, (Sk + Sk[A][:, A]) / 2  # gradient in the commutant of A


def haar(n, rng):
    z = (rng.standard_normal((n, n)) + 1j * rng.standard_normal((n, n))) / np.sqrt(2)
    q, r = np.linalg.qr(z)
    return q * (np.diag(r) / np.abs(np.diag(r)))


def random_commutant_unitary(A, rng):
    N = len(A)
    Tp, Tm = np.zeros((N, N // 2)), np.zeros((N, N // 2))
    for i, h in enumerate([h for h in range(N) if h < A[h]]):
        Tp[h, i] = Tm[h, i] = Tp[A[h], i] = 1 / np.sqrt(2)
        Tm[A[h], i] = -1 / np.sqrt(2)
    return Tp @ haar(N // 2, rng) @ Tp.T + Tm @ haar(N // 2, rng) @ Tm.T


def random_commutant_skew(A, rng):
    N = len(A)
    Z = rng.standard_normal((N, N)) + 1j * rng.standard_normal((N, N))
    Om = (Z - Z.conj().T) / 2
    Om = (Om + Om[A][:, A]) / 2
    return Om / np.linalg.norm(Om, 2)


def planted(qspec, k, A, B):
    """Q = <qa,qb,qc>; returns powered words, powers, standard-form permutation C', |Q|."""
    qa, qb, qc = [tuple(int(x) for x in g.split(",")) for g in qspec.split(";")]
    G = {"a": qa, "b": qb, "c": qc}
    assert [order(qa), order(qb), order(qc), order(comp(qa, qb)), order(comp(qa, qc))] == [2, 3, 2, 4, 3]
    H = closure([qa, qb])
    assert len(H) == 24 and len(closure([qa, qc])) == 6
    Q = closure([qa, qb, qc])
    assert (24 * k) % len(Q) == 0, "N must be divisible by |Q|"
    ords = [order(word_elem(w, G)) for w in V_WORDS]
    s4 = closure([S4A, S4B])
    e = tuple(range(len(qa)))
    wordof, frontier = {e: []}, [e]
    while frontier:
        nxt = []
        for h in frontier:
            for l in "ab":
                x = comp(G[l], h)
                if x not in wordof:
                    wordof[x] = [(l, 1)] + wordof[h]
                    nxt.append(x)
        frontier = nxt
    std = {h: s4.index(word_elem(wordof[h], {"a": S4A, "b": S4B})) for h in H}
    X, block = {}, 0
    for jj in range((24 * k) // len(Q)):
        for q in Q:
            if (q, jj) not in X:
                for h in H:
                    X[(comp(h, q), jj)] = std[h] + 24 * block
                block += 1
    assert block == k
    Cp = np.zeros(24 * k, dtype=int)
    for (q, jj), y in X.items():
        Cp[y] = X[(comp(qc, q), jj)]
        assert A[y] == X[(comp(qa, q), jj)] and B[y] == X[(comp(qb, q), jj)]
    return [w * m for w, m in zip(V_WORDS, ords)], ords, Cp, len(Q)


def run(mode, N, seed, iters, qspec=None, basin=None):
    k = N // 24
    rng = np.random.default_rng(seed)
    A, B, C0 = standard(k)
    perms, I = {"a": A, "b": B}, np.eye(N)
    Ad, Bd, C0d = dense(A), dense(B), dense(C0)
    for M, p in ((Ad, 2), (Bd, 3), (Ad @ Bd, 4), (C0d, 2), (Ad @ C0d, 3)):
        assert np.allclose(np.linalg.matrix_power(M, p), I)
    info = {}
    if mode == "V":
        words = V_WORDS
    elif mode == "planted":
        words, ords, Cp, qn = planted(qspec, k, A, B)
        ex = [word_value(syllables(w, perms), dense(Cp)) for w in words]
        info = dict(Q_order=qn, powers=ords,
                    planted_exact_max_hs=max(float(np.linalg.norm(m - I) / np.sqrt(N)) for m in ex))
    else:
        words = []
        for w in V_WORDS:
            n = {l: sum(1 for x, _ in w if x == l) for l in "abc"}
            letters = [("a", 1)] * n["a"] + [("c", 1)] * n["c"] + [("b", int(rng.choice([1, -1]))) for _ in range(n["b"])]
            rng.shuffle(letters)
            words.append(letters)
    syls = [syllables(w, perms) for w in words]
    if basin is not None:
        Om = random_commutant_skew(A, rng)
        C = expm(-basin * Om) @ dense(Cp) @ expm(basin * Om)
    else:
        W = random_commutant_unitary(A, rng)
        C = W.conj().T @ C0d @ W
    L, defs, S = loss_grad(syls, C, A)
    L0, lr, t0, hist = L, 0.5, time.time(), []
    for it in range(iters):
        E = expm(lr * S)
        nC = E @ C @ E.conj().T
        nL, ndefs, nS = loss_grad(syls, nC, A)
        if nL < L:
            C, L, defs, S, lr = nC, nL, ndefs, nS, min(lr * 1.2, 50.0)
        else:
            lr *= 0.5
            if lr < 1e-10:
                break
        if it % 100 == 0:
            hist.append((it, L))
    return dict(mode=mode, N=N, seed=seed, iters_done=it + 1, basin=basin, qspec=qspec, initial_mean_sq=L0,
                final_mean_sq=L, final_max_hs=float(np.sqrt(max(defs))), per_word_sq=defs,
                word_lengths=[len(w) for w in words], seconds=time.time() - t0,
                s3_relation_residual=float(max(np.linalg.norm(C @ C - I), np.linalg.norm(np.linalg.matrix_power(Ad @ C, 3) - I)) / np.sqrt(N)),
                history=hist, **info)


def fdcheck():
    rng = np.random.default_rng(7)
    A, B, C0 = standard(1)
    syls = [syllables(w, {"a": A, "b": B}) for w in V_WORDS]
    W = random_commutant_unitary(A, rng)
    C = W.conj().T @ dense(C0) @ W
    L, _, S = loss_grad(syls, C, A)
    Om = random_commutant_skew(A, rng)
    h = 1e-6
    Lp = loss_grad(syls, expm(-h * Om) @ C @ expm(h * Om), A)[0]
    Lm = loss_grad(syls, expm(h * Om) @ C @ expm(-h * Om), A)[0]
    return dict(numeric=(Lp - Lm) / (2 * h), predicted=float(np.real(np.trace(Om.conj().T @ S))), loss=L,
                V_word_letters=[len(w) for w in V_WORDS])


def findq(n):
    """S4-structures (qa, qb) on n points and all involutions qc with <qa,qc> = S3; record |<qa,qb,qc>|."""
    found = {}
    pts = list(range(n))
    inv_list = [p for p in itertools.permutations(pts) if comp(p, p) == tuple(pts) and p != tuple(pts)]
    s4_embeds = []
    for qa in inv_list:
        for qb in itertools.permutations(pts):
            if order(qb) == 3 and order(comp(qa, qb)) == 4 and len(closure([qa, qb])) == 24:
                s4_embeds.append((qa, qb))
                break
        if len(s4_embeds) >= 6:
            break
    for qa, qb in s4_embeds:
        for qc in inv_list:
            if order(comp(qa, qc)) == 3 and len(closure([qa, qc])) == 6:
                m = len(closure([qa, qb, qc]))
                key = str(m)
                if key not in found:
                    ords = [order(word_elem(w, {"a": qa, "b": qb, "c": qc})) for w in V_WORDS]
                    found[key] = dict(spec=";".join(",".join(map(str, g)) for g in (qa, qb, qc)), powers=ords)
    return found


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--task")
    ap.add_argument("--iters", type=int, default=3000)
    ap.add_argument("--fdcheck", action="store_true")
    ap.add_argument("--findq", type=int)
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    if a.fdcheck:
        r = fdcheck()
    elif a.findq:
        r = findq(a.findq)
    else:
        parts = a.task.split()
        kw = dict(p.split("=", 1) for p in parts[3:])
        r = run(parts[0], int(parts[1]), int(parts[2]), int(kw.get("iters", a.iters)), kw.get("Q"),
                float(kw["basin"]) if "basin" in kw else None)
    print(json.dumps({k: v for k, v in r.items() if k != "history"} if isinstance(r, dict) else r), flush=True)
    json.dump(r, open(a.out, "w"), indent=1)
