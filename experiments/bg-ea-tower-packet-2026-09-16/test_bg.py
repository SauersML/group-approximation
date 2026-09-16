#!/usr/bin/env python3
"""Check the Baumslag--Gersten Weinbaum packet in the induced tower quotient.

BG = <a,b | (a^b)^(-1) a (a^b) = a^2>, a^b = b^(-1) a b.
Relator (cyclic spelling, 9 letters, A=a^-1, B=b^-1):  B A b a B a b A A.
Tower: V = Q, a_(i+1) acts by X = 1/2, so a_(i+1)^-1 a_i a_(i+1) = a_i^2.
"""
import itertools
import random
import sys
from tower import window, word_eval, rewrite_ab

X = [[__import__('fractions').Fraction(1, 2)]]
REL = "BAbaBabAA"


def bexp(u):
    return u.count('b') - u.count('B')


def main():
    P, Q = -3, 3
    G = window(P, Q, X)
    ident = G.id
    # 1. relations a_(i+1)^-1 a_i a_(i+1) a_i^-2 = 1 inside the window
    for i in range(P, Q):
        w = [(i + 1, -1), (i, 1), (i + 1, 1), (i, -2)]
        assert word_eval(G, w) == ident, ("relation fails", i)
    print("relations hold for i in [%d,%d)" % (P, Q))
    # 2. the relator itself
    assert word_eval(G, rewrite_ab(REL)) == ident
    print("relator rewrites to identity:", rewrite_ab(REL))
    # 3. a_i nontrivial, a_i of infinite order (spot check), perfectness witness
    for i in range(P, Q + 1):
        assert word_eval(G, [(i, 1)]) != ident
    # 4. packet: all proper nonempty contiguous subwords of the cyclic spelling
    n = len(REL)
    packet = set()
    for start in range(n):
        for L in range(1, n):
            packet.add(''.join(REL[(start + k) % n] for k in range(L)))
    zero = [u for u in sorted(packet) if bexp(u) == 0]
    nonzero = [u for u in sorted(packet) if bexp(u) != 0]
    print("distinct packet words:", len(packet), " b-exp nonzero:", len(nonzero),
          " b-exp zero:", len(zero))
    dead = []
    for u in zero:
        wd = rewrite_ab(u)
        val = word_eval(G, wd)
        status = "alive" if val != ident else "DEAD"
        if val == ident:
            dead.append(u)
        print("  %-9s -> %-40s %s" % (u, wd, status))
    print("dead packet words:", dead)
    # 5. consistency: window inclusions S[-2,2] -> S[-3,3] preserve (non)triviality
    random.seed(1)
    H = window(-2, 2, X)
    mism = 0
    for _ in range(300):
        L = random.randint(1, 10)
        wd = [(random.randint(-2, 2), random.choice([1, -1])) for _ in range(L)]
        t1 = word_eval(H, wd) == H.id
        t2 = word_eval(G, wd) == G.id
        mism += (t1 != t2)
    print("window-inclusion consistency mismatches (300 random words):", mism)
    return 0 if not dead and mism == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
