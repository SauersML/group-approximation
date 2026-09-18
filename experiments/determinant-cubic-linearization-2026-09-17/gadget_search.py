"""Search for padding gadgets.

A gadget is a nonnegative integer s x s matrix G with
  G 1 = 3*1 - dR,   1^T G = 3*1^T - dC,   |dR| = |dC| = k,
  |det G| = 1, and (G^-1)_{c r} = 0 for all c in supp dC, r in supp dR.

Lemma (no scalar gadget): no such G exists for any s and k >= 1. With u = G^-1 1
(integral, since |det G| = 1) we get G^-1 dR = 3u - 1, so for c in supp dC
  sum_r (G^-1)_{c r} dR[r] = 3 u_c - 1 = -1 mod 3,
and some (G^-1)_{c r} with r in supp dR is nonzero.
The search confirms this for s <= 3 (k = 1, 2, 3) and s = 4 (k = 3), as a check on the
lemma. This is why the gadget in linearize_check.py uses the central variable s of H x Z:
G(s) = [[0,1,s],[1,1,1],[s,1,1]] has det -(1-s)^2 (Mahler measure 1) and adj(G)_{00} = 0.
"""
import itertools
import sys
from fractions import Fraction


def det_int(M):
    n = len(M)
    A = [[Fraction(x) for x in row] for row in M]
    d = Fraction(1)
    for i in range(n):
        p = next((r for r in range(i, n) if A[r][i] != 0), None)
        if p is None:
            return 0
        if p != i:
            A[i], A[p] = A[p], A[i]
            d = -d
        d *= A[i][i]
        for r in range(i + 1, n):
            f = A[r][i] / A[i][i]
            if f:
                for c in range(i, n):
                    A[r][c] -= f * A[i][c]
    return int(d)


def minor(M, r, c):
    return [[M[i][j] for j in range(len(M)) if j != c] for i in range(len(M)) if i != r]


def compositions(total, parts, cap):
    if parts == 1:
        if total <= cap:
            yield (total,)
        return
    for x in range(min(total, cap) + 1):
        for rest in compositions(total - x, parts - 1, cap):
            yield (x,) + rest


def matrices_with_margins(rows, cols):
    s = len(rows)
    M = [[0] * s for _ in range(s)]
    colrem = list(cols)

    def rec(i):
        if i == s:
            if all(x == 0 for x in colrem):
                yield [row[:] for row in M]
            return
        for comp in compositions(rows[i], s, 3):
            if all(comp[j] <= colrem[j] for j in range(s)):
                for j in range(s):
                    colrem[j] -= comp[j]
                M[i] = list(comp)
                yield from rec(i + 1)
                for j in range(s):
                    colrem[j] += comp[j]
        M[i] = [0] * s

    yield from rec(0)


def is_gadget(G, dR, dC):
    d = det_int(G)
    if abs(d) != 1:
        return False
    for r in range(len(G)):
        if dR[r] == 0:
            continue
        for c in range(len(G)):
            if dC[c] == 0:
                continue
            if det_int(minor(G, r, c)) != 0:
                return False
    return True


def search(s, k, limit=1):
    found = []
    seen_d = set()
    for dR in compositions(k, s, 3):
        # up to permutation, dR sorted decreasing
        if list(dR) != sorted(dR, reverse=True):
            continue
        for dC in compositions(k, s, 3):
            rows = [3 - x for x in dR]
            cols = [3 - x for x in dC]
            for G in matrices_with_margins(rows, cols):
                if is_gadget(G, dR, dC):
                    found.append((G, dR, dC))
                    if len(found) >= limit:
                        return found
    return found


if __name__ == "__main__":
    smax = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    for k in (1, 2):
        for s in range(1, smax + 1):
            res = search(s, k)
            print(f"k={k} s={s}: gadgets found = {len(res)} (lemma predicts 0)")
            assert not res
    for s in range(1, max(smax, 4) + 1):
        res = search(s, 3, limit=3)
        print(f"k=3 s={s}: gadgets found = {len(res)} (lemma predicts 0)")
        assert not res
    print("no scalar gadget, as the lemma predicts")
