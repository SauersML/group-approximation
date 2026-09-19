#!/usr/bin/env python3
"""Integral LLL basis of the rational W^perp (output of wperp_ratrec.py).

Usage: python3 wperp_lll.py wperp.pkl out.pkl
"""
import math
import pickle
import sys

from flint import fmpz_mat


def main(src, out):
    rows = pickle.load(open(src, "rb"))["rows"]
    Z = []
    for r in rows:
        den = 1
        for q in r:
            den = den * q.denominator // math.gcd(den, q.denominator)
        v = [int(q * den) for q in r]
        g = 0
        for x in v:
            g = math.gcd(g, x)
        Z.append([x // g for x in v])
    B = fmpz_mat(Z).lll()
    Bl = [[int(B[i, j]) for j in range(B.ncols())] for i in range(B.nrows())]
    mx = max(abs(x) for r in Bl for x in r)
    print("LLL basis", len(Bl), "x", len(Bl[0]), "max entry", mx,
          "rank", fmpz_mat(Bl).rank(), flush=True)
    pickle.dump(Bl, open(out, "wb"))


if __name__ == "__main__":
    main(*sys.argv[1:])
