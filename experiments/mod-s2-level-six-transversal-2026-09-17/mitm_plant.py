#!/usr/bin/env python3
"""Negative control for mitm.cpp: plant a transversal in a copy of its input.

A random choice T of one class per block is made to sum to 0 mod p by replacing
the row of its last class with minus the sum of the other nine rows.  A correct
exhaustive search must then report T (and the planted row is printed).

Usage: python3 mitm_plant.py mitm-p.txt planted.txt seed
"""
import random
import sys


def main(src, dst, seed):
    rnd = random.Random(int(seed))
    lines = open(src).read().split("\n")
    p, m, R = map(int, lines[0].split())
    block = [int(x) for x in lines[1].split()]
    rows = [[int(x) for x in lines[2 + c].split()] for c in range(m)]
    T = [rnd.choice([c for c in range(m) if block[c] == b]) for b in range(10)]
    s = [sum(rows[c][i] for c in T[:-1]) % p for i in range(R)]
    rows[T[-1]] = [(-x) % p for x in s]
    with open(dst, "w") as f:
        f.write(f"{p} {m} {R}\n" + " ".join(map(str, block)) + "\n")
        for r in rows:
            f.write(" ".join(map(str, r)) + "\n")
    print("planted", sorted(T))


if __name__ == "__main__":
    main(*sys.argv[1:])
