"""Numerical sanity check for the random-lift proof of
fpbs-mal-twisted-level-seed-density-uniform-witness.

L = F(a,b) acts on the right. Q_0 = {pt}. Q_{m+1} = Q_m x [N], where
(q,i).s = (q.s, sigma_{s,q}(i)) and the sigma_{s,q} are independent uniform
permutations. For each depth j the script builds t_j = phi^j(b), with
phi(a) = a and phi(b) = b a b^-2, and on every level it reports:
  n          |Q_m|
  lam        ||M_j restricted to 1-perp||, M_j = (U_a + U_a* + U_t + U_t*)/4
  lower      (1 - lam) n / 6, the proven lower bound on r(Q_m^(j)) (counting
             lemma plus expander mixing, at m = floor(n/2))
  greedy     a greedy-and-prune upper bound on r(Q_m^(j))
  ratio      greedy / n
The proof needs lam <= 0.9 < 1; Kesten's value for the free limit is
sqrt(3)/2 = 0.8660. With small N, lam may sit above the limit.
Usage: python3 random_lift_gap.py N levels jmax seed
"""
import random
import sys

import numpy as np


def reduce_word(w):
    out = []
    for x in w:
        if out and out[-1][0] == x[0] and out[-1][1] == -x[1]:
            out.pop()
        else:
            out.append(x)
    return out


def inv_word(w):
    return [(s, -e) for (s, e) in reversed(w)]


def t_word(j):
    t = [("b", 1)]
    for _ in range(j):
        t = reduce_word(t + [("a", 1)] + inv_word(t) + inv_word(t))
    return t


def lift(P, N, rng):
    """P = {'a': perm, 'b': perm} on n points; return lifted perms on n*N."""
    n = len(P["a"])
    out = {}
    for s in ("a", "b"):
        arr = np.empty(n * N, dtype=np.int64)
        for q in range(n):
            sig = list(range(N))
            rng.shuffle(sig)
            for i in range(N):
                arr[q * N + i] = P[s][q] * N + sig[i]
        out[s] = arr
    return out


def word_perm(P, w):
    n = len(P["a"])
    inv = {s: np.argsort(P[s]) for s in ("a", "b")}
    y = np.arange(n)
    for (s, e) in w:
        y = P[s][y] if e == 1 else inv[s][y]
    return y


def markov_lam(pa, pt):
    n = len(pa)
    M = np.zeros((n, n))
    idx = np.arange(n)
    for p in (pa, pt):
        U = np.zeros((n, n))
        U[idx, p] = 1.0
        M += U + U.T
    M /= 4.0
    ev = np.sort(np.linalg.eigvalsh(M))
    # remove one copy of the top eigenvalue 1 (constants)
    rest = ev[:-1]
    return float(max(abs(rest[0]), abs(rest[-1]))) if n > 1 else 0.0


def closure_size(pa, pt, S):
    n = len(pa)
    ia, it = np.argsort(pa), np.argsort(pt)
    inC = np.zeros(n, dtype=bool)
    stack = list(S)
    for x in S:
        inC[x] = True
    size = len(set(S))

    def tri_check(y, stack):
        # triple (y, y.a, y.t): if two positions in C, add the third
        z = (y, int(pa[y]), int(pt[y]))
        cnt = int(inC[z[0]]) + int(inC[z[1]]) + int(inC[z[2]])
        if cnt == 2:
            for u in z:
                if not inC[u]:
                    inC[u] = True
                    stack.append(u)
                    return 1
        return 0

    while stack:
        x = stack.pop()
        # x occurs as position 0 of triple x, position 1 of triple x.a^-1,
        # position 2 of triple x.t^-1
        for y in (x, int(ia[x]), int(it[x])):
            size += tri_check(y, stack)
    return size


def greedy_r(pa, pt, rng):
    n = len(pa)
    order = list(range(n))
    rng.shuffle(order)
    S = []
    for x in order:
        if closure_size(pa, pt, S) == n:
            break
        S.append(x)
    for x in list(S):
        T = [y for y in S if y != x]
        if closure_size(pa, pt, T) == n:
            S = T
    return len(S)


def main():
    N = int(sys.argv[1])
    levels = int(sys.argv[2])
    jmax = int(sys.argv[3])
    seed = int(sys.argv[4])
    select = len(sys.argv) > 5 and sys.argv[5] == "select"
    rng = random.Random(seed)
    tower = [{"a": np.array([0]), "b": np.array([0])}]
    tries_used = []
    for _ in range(levels):
        # "select" mimics the proof: keep a lift only if lam_j <= 0.9 for
        # every j <= jmax (the proof shows such lifts exist once N is large)
        for tries in range(1, 201):
            P = lift(tower[-1], N, rng)
            if not select:
                break
            if all(markov_lam(P["a"], word_perm(P, t_word(j))) <= 0.9
                   for j in range(jmax + 1)):
                break
        tries_used.append(tries)
        tower.append(P)
    print("N=%d levels=%d seed=%d select=%s tries=%s  Kesten sqrt(3)/2=%.4f"
          % (N, levels, seed, select, tries_used, 3 ** 0.5 / 2))
    for j in range(jmax + 1):
        tw = t_word(j)
        print("j=%d |t_j|=%d" % (j, len(tw)))
        for m, P in enumerate(tower):
            if m == 0:
                continue
            pa, pt = P["a"], word_perm(P, tw)
            n = len(pa)
            lam = markov_lam(pa, pt)
            g = greedy_r(pa, pt, rng)
            print("  m=%d n=%5d lam=%.4f lower=%7.2f greedy=%5d ratio=%.4f"
                  % (m, n, lam, (1 - lam) * n / 6, g, g / n))
    # fixed-point proportions of a few short words on the top level
    P = tower[-1]
    words = {"a": [("a", 1)], "b": [("b", 1)], "ab": [("a", 1), ("b", 1)],
             "[a,b]": [("a", 1), ("b", 1), ("a", -1), ("b", -1)]}
    for name, w in words.items():
        y = word_perm(P, w)
        print("fix-proportion %-6s %.5f" %
              (name, float(np.mean(y == np.arange(len(y))))))


if __name__ == "__main__":
    main()
