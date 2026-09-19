#!/usr/bin/env python3
"""Re-check mitm.cpp solutions in exact integer arithmetic against every prime.

Usage: python3 mitm_check.py phi.pkl mitm.out
"""
import pickle
import sys


def main(pkl, sols):
    d = pickle.load(open(pkl, "rb"))
    Phi, block = d["Phi"], d["block"]
    n, tally = 0, {}
    for ln in open(sols):
        if not ln.startswith("SOL"):
            if ln.startswith("DONE"):
                print(ln.strip())
            continue
        T = [int(x) for x in ln.split()[1:]]
        assert sorted(block[j] for j in T) == sorted(set(block)), T
        ok = tuple(p for p in Phi
                   if all(sum(Phi[p][j][k] for j in T) % p == 0
                          for k in range(len(Phi[p][0]))))
        tally[ok] = tally.get(ok, 0) + 1
        n += 1
    print(n, "solutions checked; primes satisfied ->", tally)


if __name__ == "__main__":
    main(*sys.argv[1:])
