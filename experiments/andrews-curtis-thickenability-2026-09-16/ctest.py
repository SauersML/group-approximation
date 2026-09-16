#!/usr/bin/env python3
"""Cross-check the C port (thick.c) against thicken.dfs: identical answers and
identical DFS node counts on seeded random presentations (2-3 generators,
1-3 relators, total length 4..14, monoid words, not necessarily reduced).
usage: ctest.py /path/to/thick-binary"""
import random
import subprocess
import sys
import thicken as T


def main(binary):
    rng = random.Random(916)
    cases = []
    for _ in range(1500):
        n = rng.choice([2, 3])
        gens = "xyz"[:n]
        m = rng.choice([1, 2, 3])
        total = rng.randint(max(m, 4), 14)
        cuts = sorted(rng.sample(range(1, total), m - 1)) if m > 1 else []
        lens = [b - a for a, b in zip([0] + cuts, cuts + [total])]
        cases.append(["".join(rng.choice(gens + gens.upper()) for _ in range(L)) for L in lens])
    inp = "".join(" ".join(c) + "\n" for c in cases)
    out = subprocess.run([binary], input=inp, capture_output=True, text=True, check=True).stdout.split("\n")
    bad = 0
    pos = 0
    for c, line in zip(cases, out):
        ok_c, nodes_c = map(int, line.split())
        ok, wit, nodes, K = T.thickenable(c, "orient")
        pos += ok
        if ok_c != int(ok) or nodes_c != nodes:
            bad += 1
            print("MISMATCH", c, ok, nodes, ok_c, nodes_c)
    print("cases", len(cases), "thickenable", pos, "mismatches", bad)
    return bad


if __name__ == "__main__":
    raise SystemExit(1 if main(sys.argv[1]) else 0)
