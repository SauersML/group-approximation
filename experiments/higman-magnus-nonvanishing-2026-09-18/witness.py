#!/usr/bin/env python3
"""Explicit witnesses for the all-k nonvanishing theorem (research/higman-virtually-solvable-edge-images-collapse-proof.md, Step 5).

Flavour b: kind-0 letters are gamma (typed by alpha-height), kind-1 letters are alpha.
  w_1     = [gamma, alpha]
  w_{r+1} = [w_r, x_r^n w_r x_r^-n],   x_r = gamma if r even, alpha if r odd  (x_r has kind r mod 2)
Theorem: S^b_(r-1)(w_r) != 0 for all r >= 1, and S^b_j(w_r) = 0 for j <= r-2.
This script checks the pattern exactly (unhashed nested formal sums) for r = 1..RMAX and n = 1..3.
Conventions: [x,y] = x^-1 y^-1 x y.  Letters: alpha = 1, gamma = 2, inverses negative.
"""
import sys

A, C = 1, 2


def red(w):
    out = []
    for x in w:
        if out and out[-1] == -x:
            out.pop()
        else:
            out.append(x)
    return out


def inv(w):
    return [-x for x in reversed(w)]


def comm(x, y):
    return red(inv(x) + inv(y) + x + y)


def conj(x, n, w):
    """x^n w x^-n"""
    return red([x] * n + w + [-x] * n)


def tower_b(u, R):
    """Exact S^b_0..S^b_R of the word u (running prefix sums; the final values are the S_r)."""
    PS = [dict() for _ in range(R + 1)]
    ht = 0

    def add(d, t, c):
        d[t] = d.get(t, 0) + c
        if d[t] == 0:
            del d[t]
    for x in u:
        e = 1 if x > 0 else -1
        if abs(x) == C:                      # kind 0
            prev = ('h', ht)
            add(PS[0], prev, e)
            levels = range(2, R + 1, 2)
        else:                                # kind 1
            prev = ('T',)
            levels = range(1, R + 1, 2)
            ht += e
        for r in levels:
            t = (prev, frozenset(PS[r - 1].items()))
            add(PS[r], t, e)
            prev = t
    return PS


def main():
    rmax = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    for n in (1, 2, 3):
        w = comm([C], [A])
        for r in range(1, rmax + 1):
            S = tower_b(w, r)
            pat = "".join("1" if S[j] else "0" for j in range(r + 1))
            ok = all(not S[j] for j in range(r - 1)) and bool(S[r - 1])
            print(f"n={n} r={r} |w_r|={len(w)} S^b_0..S^b_{r} nonzero pattern {pat} "
                  f"-> {'OK' if ok else 'FAIL'} (need zeros below level {r-1}, nonzero at {r-1})")
            sys.stdout.flush()
            assert ok
            if r == rmax:
                break
            x = C if r % 2 == 0 else A
            w = comm(w, conj(x, n, w))
    print("all witnesses verified")


if __name__ == "__main__":
    main()
