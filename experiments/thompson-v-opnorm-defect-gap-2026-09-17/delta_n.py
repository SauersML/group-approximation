"""Upper bounds for the operator-norm defect gap delta_n of Thompson's V (and two finite controls).

G0 = S4 *_<a> S3 = <a,b,c | a^2, b^3, (ab)^4, c^2, (ac)^3>, and V = G0/<<r5..r8>> (Bleak--Quick words,
../thompson-v-models/rel_V.txt).  For an exact unitary representation rho of G0 put
    D(rho) = max_i ||rho(r_i) - 1||_op ,
and delta_n = min { D(rho) : rho : G0 -> U(n), rho(a) != 1 }.  By the claim
thompson-v-mf-iff-opnorm-s4-s3-defect-gap-vanishes, V is MF iff delta_n -> 0, and delta_n is also the
minimum of D over nontrivial IRREDUCIBLE representations of dimension <= n.

Every rho is, up to conjugacy, (rho4, W rho3 W^*) where rho4, rho3 are fixed block sums of irreducibles
of S4 and S3 in which rho4(a) = rho3(a) = diag(1_{n-k}, -1_k), and W runs over U(n-k) x U(k), the
commutant of that diagonal.  This script enumerates every pair of multiplicity vectors with the same n
and the same k >= 1, and minimizes D over W by Adam on the exact largest eigenvalue of
(X-1)^*(X-1), with random restarts.  Results are UPPER bounds on delta_n (a local search).

Controls (same G0, same code path):
  CTRL   words trivial in S5 (a=(01), b=(123), c=(04)); exact already at n = 1 through the sign
         character of S5, so it is a weak control.
  CTRL2  words trivial in PSL(2,17) acting on 18 points; exact solutions exist at n = 9 and n = 17 (the
         Steinberg summand of the permutation representation) and not through PSL(2,17) below 9.
         calibrate_ctrl2.py tests the local search on the n = 17 Steinberg pattern.
Word convention does not matter: rho -> rho^T identifies delta_n for a word set and its reversal.

Usage: python3 delta_n.py --mode V --nmax 9 --restarts 6 --iters 400 --out out_V.json
"""
import argparse, itertools, json, os, sys, time
import numpy as np
import torch

HERE = os.path.dirname(os.path.abspath(__file__))
MODELS = os.path.join(HERE, "..", "thompson-v-models")
sys.path.insert(0, MODELS)
import texwords  # noqa: E402

torch.set_default_dtype(torch.float64)


# ---------------------------------------------------------------- irreducibles of S4 = <a,b>, S3 = <a,c>
def perm_matrix(p):
    n = len(p)
    M = np.zeros((n, n))
    for i, j in enumerate(p):
        M[j, i] = 1.0  # e_i -> e_{p(i)}
    return M


def restrict(Ms, basis):
    """Matrices of the representation on the orthonormal columns of `basis` (an invariant subspace)."""
    return [basis.T @ M @ basis for M in Ms]


def orth_complement_of_ones(n):
    Q, _ = np.linalg.qr(np.column_stack([np.ones(n)] + [np.eye(n)[:, i] for i in range(n - 1)]))
    return Q[:, 1:]


def s4_irreps():
    a, b = perm_matrix((1, 0, 2, 3)), perm_matrix((0, 2, 3, 1))
    std = restrict([a, b], orth_complement_of_ones(4))
    # S4 -> S3 through the action on the three pairings {01|23},{02|13},{03|12}
    pairings = [frozenset([frozenset([0, 1]), frozenset([2, 3])]), frozenset([frozenset([0, 2]), frozenset([1, 3])]),
                frozenset([frozenset([0, 3]), frozenset([1, 2])])]

    def on_pairings(p):
        return tuple(pairings.index(frozenset(frozenset(p[x] for x in blk) for blk in pr)) for pr in pairings)

    a3, b3 = perm_matrix(on_pairings((1, 0, 2, 3))), perm_matrix(on_pairings((0, 2, 3, 1)))
    two = restrict([a3, b3], orth_complement_of_ones(3))
    triv = [np.eye(1), np.eye(1)]
    sgn = [-np.eye(1), np.eye(1)]  # a transposition, b a 3-cycle
    stds = [-std[0], std[1]]
    return {"1": triv, "sgn": sgn, "2": two, "3": std, "3s": stds}


def s3_irreps():
    a, c = perm_matrix((1, 0, 2)), perm_matrix((0, 2, 1))
    two = restrict([a, c], orth_complement_of_ones(3))
    return {"1": [np.eye(1), np.eye(1)], "sgn": [-np.eye(1), -np.eye(1)], "2": two}


def check_relations(S4, S3):
    I = lambda n: np.eye(n)
    for name, (a, b) in S4.items():
        n = a.shape[0]
        assert np.allclose(a @ a, I(n)) and np.allclose(np.linalg.matrix_power(b, 3), I(n))
        assert np.allclose(np.linalg.matrix_power(a @ b, 4), I(n)), name
    for name, (a, c) in S3.items():
        n = a.shape[0]
        assert np.allclose(a @ a, I(n)) and np.allclose(c @ c, I(n))
        assert np.allclose(np.linalg.matrix_power(a @ c, 3), I(n)), name


def diagonalize_a(gens):
    """Conjugate so that the first generator a becomes diag(+1..., -1...)."""
    a = gens[0]
    w, U = np.linalg.eigh(a)
    order = np.argsort(-w)
    U = U[:, order]
    out = [U.T @ g @ U for g in gens]
    assert np.allclose(out[0], np.diag(np.round(np.diag(out[0]))))
    return out, int(round(np.sum(np.diag(out[0]) < 0)))


def block_sum(irr, mult):
    """Direct sum with a = diag(1_{n-k}, -1_k): collect +1 and -1 coordinates of every block."""
    blocks = []
    for name, m in mult.items():
        for _ in range(m):
            blocks.append(irr[name])
    if not blocks:
        return None
    n = sum(b[0].shape[0] for b in blocks)
    G = [np.zeros((n, n)) for _ in range(2)]
    plus, minus, off = [], [], 0
    for b in blocks:
        d = b[0].shape[0]
        for t in range(2):
            G[t][off:off + d, off:off + d] = b[t]
        diag = np.diag(b[0])
        plus += [off + i for i in range(d) if diag[i] > 0]
        minus += [off + i for i in range(d) if diag[i] < 0]
        off += d
    P = np.eye(n)[:, plus + minus]
    G = [P.T @ g @ P for g in G]
    return G, len(minus)


def patterns(irr, n):
    names = list(irr)
    dims = [irr[x][0].shape[0] for x in names]
    kdim = [int(round(np.sum(np.diag(irr[x][0]) < 0))) for x in names]
    out = []

    def rec(i, left, cur):
        if i == len(names):
            if left == 0:
                out.append(dict(zip(names, cur)))
            return
        for m in range(left // dims[i] + 1):
            rec(i + 1, left - m * dims[i], cur + [m])

    rec(0, n, [])
    return [(p, sum(p[x] * kdim[j] for j, x in enumerate(names))) for p in out]


# ---------------------------------------------------------------- words and the defect
def load_words(mode):
    fn = {"V": "rel_V.txt", "CTRL": "rel_CTRL.txt", "CTRL2": "rel_CTRL2.txt"}[mode]
    return [texwords.parse(l.strip()) for l in open(os.path.join(MODELS, fn)) if l.strip()]


def word_mats(word, A, B, C):
    Binv = B.transpose(-1, -2).conj()
    M = None
    for l, e in word:
        X = {"a": A, "c": C}[l] if l in "ac" else (B if e > 0 else Binv)
        M = X if M is None else M @ X
    return M


def syllables(word, A, B):
    """Fixed matrices P_0, ..., P_t with word = P_0 C P_1 C ... C P_t (c is an involution)."""
    n = A.shape[-1]
    Binv = B.transpose(-1, -2).conj()
    cur, out = torch.eye(n, dtype=A.dtype), []
    for l, e in word:
        if l == "c":
            out.append(cur)
            cur = torch.eye(n, dtype=A.dtype)
        else:
            cur = cur @ (A if l == "a" else (B if e > 0 else Binv))
    out.append(cur)
    return out


def defects(words, A, B, C, syls=None):
    n = A.shape[-1]
    I = torch.eye(n, dtype=A.dtype)
    out = []
    for j, w in enumerate(words):
        if syls is None:
            X = word_mats(w, A, B, C) - I
        else:
            X = syls[j][0]
            for P in syls[j][1:]:
                X = X @ C @ P
            X = X - I
        ev = torch.linalg.eigvalsh(X.transpose(-1, -2).conj() @ X)
        out.append(ev[..., -1].clamp_min(0).sqrt())
    return torch.stack(out, -1)  # (..., #words)


def skew(H):
    return 0.5 * (H - H.transpose(-1, -2).conj())


def minimize(words, A4, B4, A3, C3, k, restarts, iters, seed, beta=30.0):
    n = A4.shape[0]
    g = torch.Generator().manual_seed(seed)
    cd = torch.complex128
    A = torch.tensor(A4, dtype=cd)
    B = torch.tensor(B4, dtype=cd)
    C3t = torch.tensor(C3, dtype=cd)
    mask = torch.zeros(n, n, dtype=torch.bool)
    mask[: n - k, : n - k] = True
    mask[n - k:, n - k:] = True
    re = torch.randn(restarts, n, n, generator=g) * 1.5
    im = torch.randn(restarts, n, n, generator=g) * 1.5
    re.requires_grad_(True)
    im.requires_grad_(True)
    opt = torch.optim.Adam([re, im], lr=0.05)
    best = (np.inf, None)
    syls = [syllables(w, A, B) for w in words]
    for it in range(iters):
        H = torch.complex(re, im) * mask
        W = torch.linalg.matrix_exp(skew(H))
        C = W @ C3t @ W.transpose(-1, -2).conj()
        D = defects(words, A, B, C, syls)  # (R, #w)
        if it == 0:  # the syllable evaluation must agree with letter-by-letter evaluation
            assert torch.allclose(D, defects(words, A, B, C), atol=1e-9)
        loss = (torch.logsumexp(beta * D, -1) / beta).sum()
        opt.zero_grad()
        loss.backward()
        opt.step()
        with torch.no_grad():
            mx = D.max(-1).values
            j = int(torch.argmin(mx))
            if float(mx[j]) < best[0]:
                best = (float(mx[j]), C[j].detach().clone())
        if it == iters // 2:
            for gr in opt.param_groups:
                gr["lr"] = 0.01
    return best


def minimize_batch(words, blocks, k, restarts, iters, seed, beta=30.0, hs_warm=0):
    """All patterns with the same (n, k) at once.  blocks: list of (A4, B4, C3) numpy arrays.
    Returns, for each pattern, the smallest max-defect seen over all restarts and iterations.
    hs_warm > 0: the first hs_warm iterations minimise the smooth Frobenius loss sum_i ||r_i - 1||_F^2
    instead (a warm start used only in calibrate_ctrl2.py)."""
    P, n = len(blocks), blocks[0][0].shape[0]
    g = torch.Generator().manual_seed(seed)
    cd = torch.complex128
    A = torch.tensor(np.stack([b[0] for b in blocks]), dtype=cd)[:, None]  # (P,1,n,n)
    B = torch.tensor(np.stack([b[1] for b in blocks]), dtype=cd)[:, None]
    C3 = torch.tensor(np.stack([b[2] for b in blocks]), dtype=cd)[:, None]
    mask = torch.zeros(n, n, dtype=torch.bool)
    mask[: n - k, : n - k] = True
    mask[n - k:, n - k:] = True
    re = (torch.randn(P, restarts, n, n, generator=g) * 1.5).requires_grad_(True)
    im = (torch.randn(P, restarts, n, n, generator=g) * 1.5).requires_grad_(True)
    opt = torch.optim.Adam([re, im], lr=0.05)
    best = torch.full((P,), np.inf, dtype=torch.float64)
    syls = [syllables(w, A, B) for w in words]
    for it in range(iters):
        H = torch.complex(re, im) * mask
        W = torch.linalg.matrix_exp(skew(H))
        C = W @ C3 @ W.transpose(-1, -2).conj()
        D = defects(words, A, B, C, syls)  # (P,R,#w)
        if it == 0:
            assert torch.allclose(D, defects(words, A, B, C), atol=1e-9)
        if it < hs_warm:
            I = torch.eye(n, dtype=cd)
            loss = 0
            for j, w in enumerate(words):
                X = syls[j][0]
                for Pm in syls[j][1:]:
                    X = X @ C @ Pm
                loss = loss + ((X - I).abs() ** 2).sum()
        else:
            loss = (torch.logsumexp(beta * D, -1) / beta).sum()
        opt.zero_grad()
        loss.backward()
        opt.step()
        with torch.no_grad():
            best = torch.minimum(best, D.max(-1).values.min(-1).values)
        if it == iters // 2:
            for gr in opt.param_groups:
                gr["lr"] = 0.01
    return best.numpy()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--mode", default="V")
    ap.add_argument("--nmin", type=int, default=1)
    ap.add_argument("--nmax", type=int, default=8)
    ap.add_argument("--restarts", type=int, default=6)
    ap.add_argument("--iters", type=int, default=400)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    torch.set_num_threads(1)
    S4 = {k: diagonalize_a(v)[0] for k, v in s4_irreps().items()}
    S3 = {k: diagonalize_a(v)[0] for k, v in s3_irreps().items()}
    check_relations(S4, S3)
    words = load_words(args.mode)
    parity = [sum(1 for l, e in w if l in "ac") % 2 for w in words]  # the 1-dim rep a,c -> -1, b -> 1
    results = {"mode": args.mode, "restarts": args.restarts, "iters": args.iters, "seed": args.seed,
               "word_lengths": [len(w) for w in words], "ac_exponent_parity": parity, "n": {}}
    print(json.dumps({"word_lengths": results["word_lengths"], "ac_exponent_parity": parity}), flush=True)
    t0 = time.time()
    for n in range(args.nmin, args.nmax + 1):
        p4, p3 = patterns(S4, n), patterns(S3, n)
        best = (np.inf, None, None)
        groups = {}
        for (m4, k4), (m3, k3) in itertools.product(p4, p3):
            if k4 != k3 or k4 == 0:
                continue
            # A pattern whose S4- and S3-isotypic parts for one of the two 1-dimensional characters of G0
            # have total dimension > n contains that character as a summand; its other summands occur in
            # smaller n (delta is nonincreasing), so it is skipped (n > 1).
            if n > 1 and (m4["1"] + m3["1"] > n or m4["sgn"] + m3["sgn"] > n):
                continue
            (A4, B4), k = block_sum(S4, m4)
            (A3, C3), k_ = block_sum(S3, m3)
            assert k == k_ == k4 and np.allclose(A4, A3)
            groups.setdefault(k, []).append(((A4, B4, C3), m4, m3))
        count = sum(len(v) for v in groups.values())
        per_pattern = []
        for k, items in sorted(groups.items()):
            vals = minimize_batch(words, [it[0] for it in items], k, args.restarts, args.iters,
                                  args.seed + 7919 * n + k)
            for v, it in zip(vals, items):
                per_pattern.append(float(v))
                if v < best[0]:
                    best = (float(v), it[1], it[2])
        results["n"][n] = {"delta_upper": best[0], "patterns": count, "argmin_S4": best[1], "argmin_S3": best[2],
                           "pattern_values_sorted": sorted(per_pattern)[:10]}
        prev = [results["n"][m]["delta_upper"] for m in results["n"]]
        results["n"][n]["running_min_upper"] = min(prev)
        print(json.dumps({"n": n, **results["n"][n], "elapsed_s": round(time.time() - t0, 1)}), flush=True)
    if args.out:
        json.dump(results, open(args.out, "w"), indent=1)


if __name__ == "__main__":
    main()
