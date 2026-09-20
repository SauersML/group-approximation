"""Haar-random balanced regular gluings of S4 *_<a> S3 have relator defect -> 2.

Claim: research/thompson-v-haar-regular-gluings-have-defect-two.md.

Part 1 (exact, the only part the proof uses). Amalgam normal form of the Bleak--Quick relators
r5..r8 of V over G0 = S4 *_<a> S3 = <a,b,c | a^2, b^3, (ab)^4, c^2, (ac)^3>.  Letters a,b act on the
four cones Q = {00,01,10,11} (a = (00 01), b = (01 10 11)); letters a,c act on P = {00,01,1}
(a = (00 01), c = (1 00)).  A syllable is a maximal run of letters from one factor, evaluated to a
permutation; syllables in <a> are absorbed into a neighbour.  The word is then cyclically reduced
(conjugated) until its first and last syllables lie in different factors.  Printed: the cyclic
syllable length 2L of a conjugate of each r_i and the check that no syllable lies in <a>.

Part 2 (numerical sanity only, not used by the proof).  rho4 = lambda_S4 (x) 1_k, rho3 =
lambda_S3 (x) 1_{4k} on C^n, n = 24k, both written in a basis where a = diag(1_{12k}, -1_{12k});
sigma = (rho4, U rho3 U^*) with U = U1 (+) U2 Haar on U(12k) x U(12k).  Printed: D(sigma) =
max_i ||sigma(r_i) - 1||, and |tr sigma(r_i)^j| for j = 1, 2, 3 (normalized trace).

Usage: python3 random_gluing.py [--ks 1 2 4 8 16] [--trials 3] [--seed 1]
"""
import argparse, itertools, os, sys
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
MODELS = os.path.join(HERE, "..", "thompson-v-models")
sys.path.insert(0, MODELS)
import texwords  # noqa: E402

# ------------------------------------------------------------------ the two factors as permutations
# S4 on Q = (00, 01, 10, 11) = (0, 1, 2, 3); S3 on P = (00, 01, 1) = (0, 1, 2).
PERM = {
    4: {"a": (1, 0, 2, 3), "b": (0, 2, 3, 1)},   # a = (00 01), b = (01 10 11): 01->10->11->01
    3: {"a": (1, 0, 2), "c": (2, 1, 0)},         # a = (00 01), c = (1 00)
}
FACTOR = {"b": 4, "c": 3}                        # a lies in both


def mul(p, q):
    """(p*q)(x) = p(q(x)): apply q first.  Words act right-to-left, as matrices do."""
    return tuple(p[q[x]] for x in range(len(q)))


def inv(p):
    r = [0] * len(p)
    for i, j in enumerate(p):
        r[j] = i
    return tuple(r)


def ident(m):
    return tuple(range(m))


def gen_perm(f, g, e):
    p = PERM[f][g]
    r = ident(len(p))
    q = p if e > 0 else inv(p)
    for _ in range(abs(e)):
        r = mul(r, q)
    return r


def in_a(f, p):
    return p == ident(len(p)) or p == PERM[f]["a"]


def syllables(word):
    """List of [factor, perm] for a word given as [(gen, exp)], left to right = matrix order."""
    syl = []
    for g, e in word:
        f = FACTOR.get(g)
        if f is None:  # letter a: join the current syllable, or open an S4 one
            f = syl[-1][0] if syl else 4
        p = gen_perm(f, g, e)
        if syl and syl[-1][0] == f:
            syl[-1][1] = mul(syl[-1][1], p)
        else:
            syl.append([f, p])
    return syl


def a_elem(f, p):
    """p in <a> of factor f: return 0 (identity) or 1 (a)."""
    return 0 if p == ident(len(p)) else 1


def normalize(syl):
    """Absorb syllables in <a> into neighbours, merge equal-factor neighbours, until stable."""
    changed = True
    while changed:
        changed = False
        # merge neighbours in the same factor
        out = []
        for f, p in syl:
            if out and out[-1][0] == f:
                out[-1][1] = mul(out[-1][1], p)
                changed = True
            else:
                out.append([f, p])
        syl = out
        # absorb <a>-syllables
        for i, (f, p) in enumerate(syl):
            if in_a(f, p):
                t = a_elem(f, p)
                del syl[i]
                if t == 1:
                    if i < len(syl):          # left-multiply the right neighbour by a
                        g = syl[i][0]
                        syl[i][1] = mul(PERM[g]["a"], syl[i][1])
                    elif i > 0:               # right-multiply the left neighbour by a
                        g = syl[i - 1][0]
                        syl[i - 1][1] = mul(syl[i - 1][1], PERM[g]["a"])
                    else:                     # the whole word is a
                        syl = [[4, PERM[4]["a"]]]
                        return syl
                changed = True
                break
    return syl


def cyclic_normal_form(word):
    syl = normalize(syllables(word))
    while len(syl) >= 2 and syl[0][0] == syl[-1][0]:
        f, p = syl.pop()                      # conjugate: move the last syllable to the front
        syl[0][1] = mul(p, syl[0][1])
        syl = normalize(syl)
    return syl


def part1(words):
    ok = True
    for i, w in enumerate(words, start=5):
        syl = cyclic_normal_form(w)
        L = len(syl)
        alt = all(syl[j][0] != syl[(j + 1) % L][0] for j in range(L)) if L >= 2 else False
        none_in_a = all(not in_a(f, p) for f, p in syl)
        ok &= alt and none_in_a and L >= 2
        print(f"r{i}: word length {sum(abs(e) for _, e in w)}, cyclic syllable length {L}, "
              f"cyclically alternating {alt}, no syllable in <a> {none_in_a}")
        print("     factors:", "".join("X" if f == 4 else "Y" for f, _ in syl))
    print("PART1", "PASS" if ok else "FAIL")
    return ok


# ------------------------------------------------------------------ part 2: random gluings
def group_closure(gens):
    m = len(gens[0])
    elems = [ident(m)]
    seen = {ident(m)}
    for x in elems:
        for g in gens:
            y = mul(g, x)
            if y not in seen:
                seen.add(y)
                elems.append(y)
    return elems


def regular_rep(f):
    gens = list(PERM[f].values())
    G = group_closure(gens)
    idx = {g: i for i, g in enumerate(G)}
    N = len(G)

    def lam(p):
        M = np.zeros((N, N))
        for h in G:
            M[idx[mul(p, h)], idx[h]] = 1.0
        return M

    a = PERM[f]["a"]
    plus, minus, done = [], [], set()
    for h in G:
        if h in done:
            continue
        ah = mul(a, h)
        done |= {h, ah}
        v = np.zeros(N); v[idx[h]] = 1; v[idx[ah]] = 1
        w = np.zeros(N); w[idx[h]] = 1; w[idx[ah]] = -1
        plus.append(v / np.sqrt(2)); minus.append(w / np.sqrt(2))
    B = np.column_stack(plus + minus)
    return {g: B.T @ lam(p) @ B for g, p in PERM[f].items()}, N


def haar(m, rng):
    Z = (rng.standard_normal((m, m)) + 1j * rng.standard_normal((m, m))) / np.sqrt(2)
    Q, R = np.linalg.qr(Z)
    return Q * (np.diag(R) / np.abs(np.diag(R)))


def blockify(M, h, k):
    """M acts on C^{2h} = E+ (+) E- (h each); return the matrix of M (x) 1_k on (E+ (x) C^k) (+) (E- (x) C^k)."""
    out = np.zeros((2 * h * k, 2 * h * k), dtype=complex)
    for s in range(2):
        for t in range(2):
            out[s * h * k:(s + 1) * h * k, t * h * k:(t + 1) * h * k] = np.kron(M[s * h:(s + 1) * h, t * h:(t + 1) * h], np.eye(k))
    return out


def word_matrix(word, mats, n):
    X = np.eye(n, dtype=complex)
    for g, e in word:
        M = mats[g] if e > 0 else mats[g].conj().T
        for _ in range(abs(e)):
            X = X @ M
    return X


def part2(words, ks, trials, seed):
    rng = np.random.default_rng(seed)
    R4, N4 = regular_rep(4)
    R3, N3 = regular_rep(3)
    for k in ks:
        n = 24 * k
        h4, h3 = N4 // 2, N3 // 2
        A4 = {g: blockify(M, h4, k) for g, M in R4.items()}
        A3 = {g: blockify(M, h3, 4 * k) for g, M in R3.items()}
        assert np.allclose(A4["a"], A3["a"])
        for t in range(trials):
            m = n // 2
            U = np.zeros((n, n), dtype=complex)
            U[:m, :m] = haar(m, rng); U[m:, m:] = haar(m, rng)
            mats = {"a": A4["a"], "b": A4["b"], "c": U @ A3["c"] @ U.conj().T}
            I = np.eye(n)
            rel = max(np.linalg.norm(x, 2) for x in [
                mats["a"] @ mats["a"] - I, np.linalg.matrix_power(mats["b"], 3) - I,
                np.linalg.matrix_power(mats["a"] @ mats["b"], 4) - I, mats["c"] @ mats["c"] - I,
                np.linalg.matrix_power(mats["a"] @ mats["c"], 3) - I])
            ds, moms = [], []
            for w in words:
                X = word_matrix(w, mats, n)
                ds.append(np.linalg.norm(X - I, 2))
                moms.append([abs(np.trace(np.linalg.matrix_power(X, j))) / n for j in (1, 2, 3)])
            print(f"n={n:4d} trial {t}: G0-relations err {rel:.1e}  ||sigma(r_i)-1|| = "
                  + " ".join(f"{d:.4f}" for d in ds) + f"  D = {max(ds):.4f}  max|tr r^j| = {np.max(moms):.4f}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--ks", type=int, nargs="*", default=[1, 2, 4, 8, 16])
    ap.add_argument("--trials", type=int, default=3)
    ap.add_argument("--seed", type=int, default=1)
    args = ap.parse_args()
    words = [texwords.parse(l.strip()) for l in open(os.path.join(MODELS, "rel_V.txt")) if l.strip()]
    part1(words)
    part2(words, args.ks, args.trials, args.seed)


if __name__ == "__main__":
    main()
