#!/usr/bin/env python3
"""Pure-braid toolkit for PMod(S_{0,6}) = P_5 / <Delta^2>, verified in the
faithful Artin representation B_5 -> Aut(F_5).

Letters: sigma-words use +-k (k = 1..4 for sigma_k); pure words use +-(p+1)
for the pair index p of A_ij, 1 <= i < j <= 5 (Birman's convention
A_ij = s_{j-1} ... s_{i+1} s_i^2 s_{i+1}^-1 ... s_{j-1}^-1).

Every identity used downstream (Artin's presentation of P_5, the Delta^2
word, the sigma-conjugation rewriting table, the full-twist words) is checked
here as an identity of automorphisms of F_5, so no sign convention is taken
on trust.
"""
import itertools

N = 5
PAIRS = [(i, j) for i in range(1, N + 1) for j in range(i + 1, N + 1)]
PIDX = {p: k for k, p in enumerate(PAIRS)}


# ---------------------------------------------------------------- free group
def fred(w):
    out = []
    for a in w:
        if out and out[-1] == -a:
            out.pop()
        else:
            out.append(a)
    return tuple(out)


def finv(w):
    return tuple(-a for a in reversed(w))


def sigma_images(k, sign):
    """Images of x_1..x_N under sigma_k^{sign} (letters +-1..+-N)."""
    img = {m: (m,) for m in range(1, N + 1)}
    if sign > 0:
        img[k] = (k, k + 1, -k)
        img[k + 1] = (k,)
    else:
        img[k] = (k + 1,)
        img[k + 1] = (-(k + 1), k, k + 1)
    return img


def subst(w, img):
    out = []
    for a in w:
        out.extend(img[a] if a > 0 else finv(img[-a]))
    return fred(out)


IDAUT = tuple((m,) for m in range(1, N + 1))


def compose(f, g):
    """(f o g)(x) = f(g(x)); automorphisms as tuples of images."""
    img = {m + 1: f[m] for m in range(N)}
    return tuple(subst(g[m], img) for m in range(N))


SIG = {}
for _k in range(1, N):
    for _s in (1, -1):
        im = sigma_images(_k, _s)
        SIG[_s * _k] = tuple(im[m] for m in range(1, N + 1))


def aut_sigma(word):
    """Homomorphism word -> Aut(F_N): phi(uv) = phi(u) o phi(v)."""
    f = IDAUT
    for a in word:
        f = compose(f, SIG[a])
    return f


def a_sigma_word(i, j):
    left = list(range(j - 1, i, -1))
    return tuple(left + [i, i] + [-k for k in reversed(left)])


def pure_to_sigma(word):
    out = []
    for a in word:
        i, j = PAIRS[abs(a) - 1]
        w = a_sigma_word(i, j)
        out.extend(w if a > 0 else finv(w))
    return tuple(out)


def aut_pure(word):
    return aut_sigma(pure_to_sigma(word))


def A(i, j, e=1):
    return e * (PIDX[(i, j)] + 1)


# ---------------------------------------------------------- P_5 presentation
def artin_relations():
    """Birman Lemma 1.8.2: A_rs^-1 A_ij A_rs = (case formula).  Returned as
    pairs (u, v) of pure words with u = v; each is verified in Aut(F_5)."""
    rels = []
    for (r, s) in PAIRS:
        for (i, j) in PAIRS:
            if (r, s) == (i, j):
                continue
            lhs = (A(r, s, -1), A(i, j), A(r, s))
            if s < i or (i < r and s < j):
                rhs = (A(i, j),)
            elif s == i:
                rhs = (A(r, j), A(i, j), A(r, j, -1))
            elif i == r and s < j:
                rhs = (A(r, j), A(s, j), A(i, j), A(s, j, -1), A(r, j, -1))
            elif r < i < s < j:
                rhs = (A(r, j), A(s, j), A(r, j, -1), A(s, j, -1), A(i, j),
                       A(s, j), A(r, j), A(s, j, -1), A(r, j, -1))
            else:
                continue
            rels.append((lhs, rhs))
    return rels


def delta2_pure():
    w = []
    for j in range(2, N + 1):
        for i in range(1, j):
            w.append(A(i, j))
    return tuple(w)


def full_twist_sigma(n):
    return tuple(list(range(1, n)) * n)


def check_presentation():
    bad = 0
    rels = artin_relations()
    for u, v in rels:
        if aut_pure(u) != aut_pure(v):
            bad += 1
    assert bad == 0, f"{bad} Artin relations fail"
    assert aut_pure(delta2_pure()) == aut_sigma(full_twist_sigma(N))
    # braid relations sanity
    for k in range(1, N - 1):
        assert aut_sigma((k, k + 1, k)) == aut_sigma((k + 1, k, k + 1))
    return rels


# ------------------------------------------ sigma-conjugation rewriting table
def conj_table():
    """For each sigma_k^{e} and A_p, a pure word equal to
    s_k^{e} A_p s_k^{-e}.  Found by search among c A_q^{+-1} c^-1, |c| <= 2."""
    letters = [a for p in range(len(PAIRS)) for a in (p + 1, -(p + 1))]
    cands = [()] + [(a,) for a in letters] + \
        [(a, b) for a in letters for b in letters if b != -a]
    cache = {}
    table = {}
    for k in range(1, N):
        for e in (1, -1):
            for p in range(len(PAIRS)):
                target = aut_sigma((e * k,) + pure_to_sigma((p + 1,)) +
                                   (-e * k,))
                found = None
                for c in cands:
                    for q in range(len(PAIRS)):
                        w = fred(c + (q + 1,) + finv(c))
                        if w not in cache:
                            cache[w] = aut_pure(w)
                        if cache[w] == target:
                            found = w
                            break
                    if found is not None:
                        break
                assert found is not None, (k, e, p)
                table[(e * k, p + 1)] = found
    return table


def conj_pure_by_sigma(gamma, word, table):
    """Pure word for gamma * word * gamma^-1 (gamma a sigma-word)."""
    w = tuple(word)
    for a in reversed(gamma):
        out = []
        for b in w:
            img = table[(a, abs(b))]
            out.extend(img if b > 0 else finv(img))
        w = fred(out)
    return w


TRIPLES = list(itertools.combinations(range(1, N + 1), 3))


def standard_twists(table):
    """Pure word T_A (Dehn twist about a round curve around A, puncture 6
    outside) for each 3-subset A of {1..5}, as gamma T_123 gamma^-1."""
    t123 = (A(1, 2), A(1, 3), A(2, 3))
    assert aut_pure(t123) == aut_sigma((1, 2) * 3)
    out = {}
    for tri in TRIPLES:
        # gamma: braid whose permutation sends {1,2,3} onto tri, built by
        # moving strand positions one step at a time (positive sigmas).
        gamma = []
        pos = [1, 2, 3]
        for idx in (2, 1, 0):
            while pos[idx] < tri[idx]:
                gamma.append(pos[idx])
                pos[idx] += 1
        gamma = tuple(reversed(gamma))
        w = conj_pure_by_sigma(gamma, t123, table)
        assert aut_pure(w) == aut_sigma(gamma + (1, 2) * 3 + finv(gamma))
        ab = [0] * len(PAIRS)
        for a in w:
            ab[abs(a) - 1] += 1 if a > 0 else -1
        want = [1 if (p[0] in tri and p[1] in tri) else 0 for p in PAIRS]
        assert ab == want, (tri, ab)
        out[tri] = w
    return out


def strand_permutation(sigma_word):
    perm = list(range(N + 1))
    for a in sigma_word:
        k = abs(a)
        perm[k], perm[k + 1] = perm[k + 1], perm[k]
    return perm


if __name__ == "__main__":
    rels = check_presentation()
    print("Artin relations verified:", len(rels))
    tab = conj_table()
    print("conjugation table entries:", len(tab))
    tw = standard_twists(tab)
    for t, w in tw.items():
        print(t, len(w))
