#!/usr/bin/env python3
"""Finite-level check of the combinatorics behind Moore's refutation
(arXiv:1807.05469, Section 2) on the free magma T on one generator.

Trees are nested tuples: LEAF = () and a*b = (a, b); #(s) = number of leaves.
Sets, defined by simultaneous recursion on #:
    T_0 = T,  T_{p+1} = (T \\ Z) * T_p,
    s in Z  iff  s = a*b with b in T_{#a}.
Checked for all trees with at most N leaves:
  (1) T_{p+1} is contained in T_p (monotonicity, used in the r > 0 case);
  (2) for every s, {t : s*t in Z} = T_{#s}   (section identity, both cases);
  (3) Z meets both classes of the parity homomorphism f(1)=0, f(a*b)=1-f(b),
      and so does its complement (sanity: Z is not read off that finite quotient).
It also prints the density of Z and T_1..T_3 among size-n trees.
Run: python3 check_moore_z_set.py [N]   (default N = 11). Exit 0 iff no failure.
"""
import sys
from functools import lru_cache

N = int(sys.argv[1]) if len(sys.argv) > 1 else 11
LEAF = ()


@lru_cache(maxsize=None)
def trees(n):
    if n == 1:
        return (LEAF,)
    out = []
    for i in range(1, n):
        for a in trees(i):
            for b in trees(n - i):
                out.append((a, b))
    return tuple(out)


@lru_cache(maxsize=None)
def size(s):
    return 1 if s == LEAF else size(s[0]) + size(s[1])


@lru_cache(maxsize=None)
def in_T(p, s):
    if p == 0:
        return True
    if s == LEAF:
        return False
    a, b = s
    return (not in_Z(a)) and in_T(p - 1, b)


@lru_cache(maxsize=None)
def in_Z(s):
    if s == LEAF:
        return False
    a, b = s
    return in_T(size(a), b)


def parity(s):
    return 0 if s == LEAF else 1 - parity(s[1])


def main():
    fails = 0
    for n in range(1, N + 1):
        for s in trees(n):
            for p in range(0, N + 1):
                if in_T(p + 1, s) and not in_T(p, s):
                    fails += 1
                    print("monotonicity fails", p, s)
    for n in range(1, N):
        for s in trees(n):
            for m in range(1, N - n + 1):
                for t in trees(m):
                    if in_Z((s, t)) != in_T(n, t):
                        fails += 1
                        print("section identity fails", s, t)
    seen = set()
    for n in range(2, N + 1):
        for s in trees(n):
            seen.add((parity(s), in_Z(s)))
    print("parity x Z classes met:", sorted(seen))
    if len(seen) != 4:
        fails += 1
    for n in range(1, N + 1):
        ts = trees(n)
        z = sum(in_Z(s) for s in ts) / len(ts)
        tp = [sum(in_T(p, s) for s in ts) / len(ts) for p in range(1, 4)]
        print(f"n={n:2d} |T_n|={len(ts):6d}  frac Z={z:.4f}  frac T_1..3="
              + " ".join(f"{x:.4f}" for x in tp))
    print("FAILURES:", fails)
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
