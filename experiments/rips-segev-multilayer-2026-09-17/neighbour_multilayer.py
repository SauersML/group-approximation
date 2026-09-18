#!/usr/bin/env python3
"""Finite-group calibration of the multi-layer neighbour lemma
(rips-segev-sparse-a-support-elements-are-regular-proof, Lemmas 2 and 3).

beta = sum_{j in J} u_j(x) y^j, with J a finite set of integers (any number of y-layers,
any exponents) and each u_j a polynomial in x with exponents in a finite set S.  Put
N_S = (S - S) minus {0} and N_J = (J - J) minus {0}.  If dim span{u_j} >= 2, then for every
alpha != 0 with alpha beta = 0 the lemma says that V = union_j supp(alpha u_j(x)) is nonempty and
  (Y_J) every p in V has p y^e in V for some e in N_J;
  (X_S) every p in V has p x^n in V for some n in N_S,
provided ord(x) > 2 span(S) (windows do not wrap) and ord(y) > span(J) (so y^e != 1 on N_J).
Both S contiguous ([0, d]) and S sparse ({0, 3}, {0, 1, 4}, ...) are tested.

The script computes full left kernels of right multiplication by beta over GF(p), checks (Y_J)
and (X_S) on every basis vector and on random kernel combinations, closes the alternating walk
x^{n_1} y^{e_1} ... x^{n_L} y^{e_L} = 1, and checks that the word is trivial with n_k in N_S and
e_k in N_J.

Both roles (x, y) = (a, b) and (b, a) are tested.  In the theorem the role (x, y) = (b, a)
is the right-annihilator case after the anti-involution: there the a-exponents are the layer set.

'dep1' counts betas whose u_j span a line (these factor and are excluded from the lemma); for
them the script records how often (X_S) fails, which shows that the rank hypothesis is needed.

Usage: python3 neighbour_multilayer.py [seed]
"""
import random
import sys


def pmul(p, q):  # apply p then q (right action): (p*q)[i] = q[p[i]]
    return tuple(q[i] for i in p)


def pinv(p):
    r = [0] * len(p)
    for i, j in enumerate(p):
        r[j] = i
    return tuple(r)


def closure(gens):
    n = len(gens[0])
    e = tuple(range(n))
    seen = {e}
    frontier = [e]
    while frontier:
        nxt = []
        for g in frontier:
            for s in gens:
                h = pmul(g, s)
                if h not in seen:
                    seen.add(h)
                    nxt.append(h)
        frontier = nxt
    return sorted(seen)


def order(g):
    e = tuple(range(len(g)))
    k, h = 1, g
    while h != e:
        h = pmul(h, g)
        k += 1
    return k


def left_kernel(G, idx, beta, P):
    """Basis of {alpha : alpha beta = 0} over GF(P). beta: dict element -> coeff."""
    N = len(G)
    # alpha beta (g) = sum_x alpha(x) beta(s) over x s = g.  Row x of M: M[x][idx[x s]] += beta(s).
    rows = []
    for x in G:
        r = [0] * N
        for s, c in beta.items():
            j = idx[pmul(x, s)]
            r[j] = (r[j] + c) % P
        rows.append(r)
    # left kernel of M = kernel of M^T: solve sum_x alpha_x rows[x] = 0.
    # Gaussian elimination on augmented [M | I].
    A = [rows[i][:] + [1 if k == i else 0 for k in range(N)] for i in range(N)]
    piv_row = 0
    for col in range(N):
        pr = None
        for r in range(piv_row, N):
            if A[r][col] % P:
                pr = r
                break
        if pr is None:
            continue
        A[piv_row], A[pr] = A[pr], A[piv_row]
        inv = pow(A[piv_row][col], P - 2, P)
        A[piv_row] = [(v * inv) % P for v in A[piv_row]]
        for r in range(N):
            if r != piv_row and A[r][col] % P:
                f = A[r][col]
                A[r] = [(vr - f * vp) % P for vr, vp in zip(A[r], A[piv_row])]
        piv_row += 1
    return [A[r][N:] for r in range(piv_row, N)]


def rmul(G, idx, alpha, elt_coeffs, P):
    out = {}
    for i, c in enumerate(alpha):
        if c:
            for s, d in elt_coeffs.items():
                g = pmul(G[i], s)
                out[g] = (out.get(g, 0) + c * d) % P
    return {g: c for g, c in out.items() if c}


def random_perm(n, rng):
    p = list(range(n))
    rng.shuffle(p)
    return tuple(p)




def rank_mod(rows, P):
    M = [r[:] for r in rows]
    rk, col, ncol = 0, 0, len(M[0]) if M else 0
    while rk < len(M) and col < ncol:
        pr = next((r for r in range(rk, len(M)) if M[r][col] % P), None)
        if pr is None:
            col += 1
            continue
        M[rk], M[pr] = M[pr], M[rk]
        inv = pow(M[rk][col], P - 2, P)
        M[rk] = [(v * inv) % P for v in M[rk]]
        for r in range(len(M)):
            if r != rk and M[r][col] % P:
                f = M[r][col]
                M[r] = [(a - f * b) % P for a, b in zip(M[r], M[rk])]
        rk += 1
        col += 1
    return rk


def powtab(g, s):
    e = tuple(range(len(g)))
    gi = pinv(g)
    t = {0: e}
    for n in range(1, s + 1):
        t[n] = pmul(t[n - 1], g)
        t[-n] = pmul(t[-(n - 1)], gi)
    return t


def diffs(S):
    return sorted({i - j for i in S for j in S if i != j}, key=lambda v: (abs(v), v))


def support_V(G, idx, alpha, us, S, J, xp, P):
    V = set()
    for j in J:
        ue = {}
        for i, c in zip(S, us[j]):
            if c:
                ue[xp[i]] = (ue.get(xp[i], 0) + c) % P
        V |= set(rmul(G, idx, alpha, ue, P))
    return V


def check(G, idx, x, y, alpha, us, S, J, P):
    """Returns (V nonempty, lemma ok, walk ok)."""
    xp = powtab(x, 2 * (max(S) - min(S)))
    yp = powtab(y, max(J) - min(J))
    V = support_V(G, idx, alpha, us, S, J, xp, P)
    if not V:
        return False, True, True
    NS, NJ = diffs(S), diffs(J)
    ok = True
    ystep, xstep = {}, {}
    for p in V:
        e = next((e for e in NJ if pmul(p, yp[e]) in V), None)
        n = next((n for n in NS if pmul(p, xp[n]) in V), None)
        if e is None or n is None:
            ok = False
        ystep[p], xstep[p] = e, n
    if not ok:
        return True, False, False
    p = next(iter(V))
    seen, word = {}, []
    while p not in seen:
        seen[p] = len(word)
        n = xstep[p]
        q = pmul(p, xp[n])
        e = ystep[q]
        word.append((n, e))
        p = pmul(q, yp[e])
    g = tuple(range(len(x)))
    for n, e in word[seen[p]:]:
        g = pmul(pmul(g, xp[n]), yp[e])
    walk_ok = g == tuple(range(len(x))) and all(n in NS and e in NJ for n, e in word[seen[p]:])
    return True, True, walk_ok


def xs_holds(G, idx, x, alpha, us, S, J, P):
    xp = powtab(x, 2 * (max(S) - min(S)))
    V = support_V(G, idx, alpha, us, S, J, xp, P)
    return all(any(pmul(p, xp[n]) in V for n in diffs(S)) for p in V)


LAYER_SETS = [(0, 1), (0, 1, 2), (0, 1, 3), (-1, 0, 2), (0, 2), (0, 1, 2, 3), (0, 3)]
EXP_SETS = [(0, 1), (0, 1, 2), (0, 2), (0, 3), (0, 1, 4), (0, 2, 3)]


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    rng = random.Random(seed)
    st = dict(configs=0, sparse_configs=0, betas=0, betas_with_kernel=0, vectors=0, empty_V=0,
              lemma_fail=0, walk_fail=0, dep1_betas=0, dep1_vectors=0, dep1_xs_fail=0)
    tried = 0
    while st["configs"] < 60 and tried < 6000:
        tried += 1
        n = rng.choice([4, 5, 6])
        a, b = random_perm(n, rng), random_perm(n, rng)
        G = closure([a, b])
        if len(G) > 130 or len(G) < 8:
            continue
        idx = {g: i for i, g in enumerate(G)}
        for (x, y) in [(a, b), (b, a)]:
            ox, oy = order(x), order(y)
            S = rng.choice(EXP_SETS)
            J = rng.choice(LAYER_SETS)
            if ox <= 2 * (max(S) - min(S)) or oy <= max(J) - min(J):
                continue
            st["configs"] += 1
            if len(S) < max(S) - min(S) + 1:
                st["sparse_configs"] += 1
            xp = powtab(x, max(S))
            yp = powtab(y, max(abs(j) for j in J))
            for P in (2, 3, 5):
                for trial in range(10):
                    us = {j: [rng.randrange(P) for _ in S] for j in J}
                    if trial % 5 == 4:  # a rank-one family, to test the hypothesis
                        base = [rng.randrange(P) for _ in S]
                        us = {j: [(rng.randrange(1, P) * c) % P for c in base] for j in J}
                    if any(not any(us[j]) for j in J):
                        continue
                    rk = rank_mod([us[j] for j in J], P)
                    beta = {}
                    for j in J:
                        for i, c in zip(S, us[j]):
                            if c:
                                g = pmul(xp[i], yp[j])
                                beta[g] = (beta.get(g, 0) + c) % P
                    beta = {g: c for g, c in beta.items() if c}
                    if not beta:
                        continue
                    K = left_kernel(G, idx, beta, P)
                    vecs = list(K)
                    for _ in range(4 if K else 0):
                        v = [0] * len(G)
                        for kv in K:
                            c = rng.randrange(P)
                            v = [(vi + c * ki) % P for vi, ki in zip(v, kv)]
                        if any(v):
                            vecs.append(v)
                    if rk < 2:
                        st["dep1_betas"] += 1
                        for v in vecs:
                            st["dep1_vectors"] += 1
                            if not xs_holds(G, idx, x, v, us, S, J, P):
                                st["dep1_xs_fail"] += 1
                        continue
                    st["betas"] += 1
                    if K:
                        st["betas_with_kernel"] += 1
                    for v in vecs:
                        st["vectors"] += 1
                        ne, ok, wok = check(G, idx, x, y, v, us, S, J, P)
                        if not ne:
                            st["empty_V"] += 1
                        elif not ok:
                            st["lemma_fail"] += 1
                        elif not wok:
                            st["walk_fail"] += 1
    print("seed", seed, st)


if __name__ == "__main__":
    main()
