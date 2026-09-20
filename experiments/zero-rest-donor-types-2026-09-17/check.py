"""Calibration for few-rest-type-reduction-is-per-group-binary-descent.

1. Over G = C_n, for random local rules on A^M (M = {0, 1, n-1}), the zero-rest
   split (Z empty, B = A, d = 1) satisfies (D1), (D2) and self-relaying on every
   configuration.  This is a check of the definitions only: over a finite group
   no automaton is strict.
2. Item 3 arithmetic: for every admissible type (1, b) with b odd, or (2, b)
   with 4 not dividing b, and every product P of a finite set of odd primes,
   the chosen t gives n = z + b t with 4 not dividing n and n = z (mod p) for
   every p dividing P.
"""
import itertools
import random


def check_zero_rest(n, k, trials=30):
    M = [0, 1, n - 1]
    A = list(range(k))
    for _ in range(trials):
        table = {u: random.choice(A) for u in itertools.product(A, repeat=len(M))}
        B = set(A)                # all symbols active
        d = {u: 0 for u in table}  # donor offset 0, i.e. the site itself
        for ell in itertools.product(A, repeat=n):
            win = lambda g: tuple(ell[(g + m) % n] for m in M)
            out = [table[win(g)] for g in range(n)]
            donors = {}
            for g in range(n):
                assert out[g] in B
                h = (g + d[win(g)]) % n                 # donor site g * d(u)
                assert ell[h] in B                      # (D1)
                donors.setdefault(h, []).append(g)
                if ell[g] in B:                         # self-relaying
                    assert out[g] in B and d[win(g)] == 0
            for h in range(n):
                if ell[h] in B:
                    assert h in donors                  # (D2)
    return True


def odd_primes(limit):
    ps = []
    for q in range(3, limit):
        if all(q % r for r in range(2, int(q ** 0.5) + 1)):
            ps.append(q)
    return ps


def check_arith(bmax=200):
    ps = odd_primes(40)
    for r in range(1, 4):
        for S in itertools.combinations(ps, r):
            P = 1
            for p in S:
                P *= p
            for b in range(1, bmax):
                types = []
                if b % 2 == 1:
                    types.append((1, b, 2 * P))
                    types.append((2, b, P))
                elif b % 4 == 2:
                    types.append((2, b, 2 * P))
                for z, bb, t in types:
                    m = z + bb * t
                    assert m % 4 != 0, (z, bb, t)
                    assert all(m % p == z % p for p in S), (z, bb, t)
                    assert all(m % p != 0 for p in S)
    return True


if __name__ == "__main__":
    random.seed(1)
    for n in (3, 4, 5):
        for k in (2, 3):
            check_zero_rest(n, k)
    print("zero-rest split: (D1), (D2), self-relaying hold on C_3, C_4, C_5, k = 2, 3")
    check_arith()
    print("item 3 arithmetic holds for b < 200 and up to three odd primes below 40")
