#!/usr/bin/env python3
"""Triage: which one-relator groups <a,b | r> of a list are already virtually compact special.

Sufficient test used (a theorem chain, not a heuristic):
  C'(1/6)  (every piece of the symmetrized closure has length < |r|/6)
    => hyperbolic (Greendlinger/Gromov) and cubulated (Wise, GAFA 2004)
    => virtually compact special (Agol 2013).
For such G, Fisher--Sanchez-Peralta already give Hughes-free division rings for k[G] in every
characteristic; only the crossed-product statement of the class H is new.

Everything else is reported 'undecided' (not 'not VCS').

Usage: vcs_triage.py FILE   (FILE: lines whose 2nd field is a word in a,b,A,B; e.g. census output)
       vcs_triage.py -w WORD ...
"""
import sys


def parse(s):
    return tuple((0 if c in "aA" else 1, 1 if c.islower() else -1) for c in s)


def inv(w):
    return tuple((a, -e) for a, e in reversed(w))


def symmetrized(w):
    n = len(w)
    out = set()
    for ww in (w, inv(w)):
        for i in range(n):
            out.add(ww[i:] + ww[:i])
    return sorted(out)


def max_piece(w):
    R = symmetrized(w)
    best = 0
    for i in range(len(R)):
        for j in range(i + 1, len(R)):
            u, v = R[i], R[j]
            k = 0
            while k < len(u) and u[k] == v[k]:
                k += 1
            best = max(best, k)
    return best


def c_prime_sixth(w):
    return 6 * max_piece(w) < len(w)


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "-w":
        words = sys.argv[2:]
    else:
        words = []
        for line in open(sys.argv[1]):
            f = line.split()
            if len(f) >= 2 and f[0].isdigit() and set(f[1]) <= set("abAB"):
                words.append(f[1])
    nv = 0
    for s in words:
        w = parse(s)
        p = max_piece(w)
        ok = 6 * p < len(w)
        nv += ok
        print("%-16s len %2d  max piece %d  %s" % (s, len(w), p, "C'(1/6) => VCS" if ok else "undecided"))
    print("# %d of %d are C'(1/6), hence virtually compact special" % (nv, len(words)))


if __name__ == "__main__":
    main()
