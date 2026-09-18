#!/usr/bin/env python3
"""Driver: relators of Pi_R(2,N) -> C low-index enumerator -> image orders.

Usage: python3 census.py N R nmax [binary]
The C source is lowindex.c (gcc -O2 -o <binary> lowindex.c).
"""
import os
import subprocess
import sys
from math import factorial

from lowindex import relators, schreier_sims_order, factor


def main():
    N, R, nmax = map(int, sys.argv[1:4])
    here = os.path.dirname(os.path.abspath(__file__))
    binary = sys.argv[4] if len(sys.argv) > 4 else os.path.join(here, "lowindex")
    if not os.path.exists(binary):
        subprocess.check_call(["gcc", "-O2", "-o", binary, os.path.join(here, "lowindex.c")])
    rels = relators(2, N, R)
    inp = f"{nmax} {len(rels)}\n" + "\n".join(
        f"{len(r)} " + " ".join(map(str, r)) for r in rels) + "\n"
    print(f"Pi_{R}(2,{N}): {len(rels)} relator classes, max length {max(map(len, rels))}, degree <= {nmax}")
    sys.stdout.flush()
    proc = subprocess.run([binary], input=inp, capture_output=True, text=True)
    stats = {}
    for line in proc.stdout.splitlines():
        v = list(map(int, line.split()))
        k = v[0]
        a = tuple(v[1:1 + k])
        b = tuple(v[1 + k:1 + 2 * k])
        o = schreier_sims_order([a, b], k)
        stats.setdefault(k, []).append(o)
    for k in sorted(stats):
        orders = stats[k]
        parts = []
        for o in sorted(set(orders)):
            tag = str(factor(o))
            if o == factorial(k) // 2:
                tag += "=|A_%d|" % k
            parts.append(f"{o} {tag} x{orders.count(o)}")
        print(f"degree {k}: {len(orders)} reps; image orders: " + "; ".join(parts))
    print(proc.stderr.strip())


if __name__ == "__main__":
    main()
