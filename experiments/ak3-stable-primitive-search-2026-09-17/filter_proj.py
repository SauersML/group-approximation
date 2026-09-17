#!/usr/bin/env python3
"""filter_proj.py -- which projections are NOT in the rank-2 component of AK(3)?

usage: filter_proj.py CAP2 < pzproj-output
Closes the rank-2 component of AK(3) under the same moves (rank 2: Whitehead automorphisms and
signed permutations of F(x,y), AC products with letter conjugators), total length <= CAP2, and
prints every PROJ line whose pair (up to rotation, inversion, order, signed permutation of x,y,z)
lies outside it.
"""
import sys
from verify_chain import neighbours, signed_perms, subst, pform

P3 = list(signed_perms(3))


def canon(p, q):
    return min(pform(subst(p, s), subst(q, s)) for s in P3)


def component(cap):
    seen, queue = set(), []

    def add(p, q):
        c = canon(p, q)
        if c not in seen:
            seen.add(c)
            queue.append((p, q))

    add("xxxYYYY", "xyxYXY")
    i = 0
    while i < len(queue):
        p, q = queue[i]
        i += 1
        for a, b in neighbours(p, q, 2):
            if a and b and len(a) + len(b) <= cap:
                add(a, b)
    return seen


def main():
    cap2 = int(sys.argv[1])
    comp = component(cap2)
    print(f"rank-2 component of AK(3) at cap {cap2}: {len(comp)} states")
    n = out = 0
    for line in sys.stdin:
        if not line.startswith("PROJ"):
            continue
        _, L, a, b = line.split()
        n += 1
        if canon(a, b) not in comp:
            out += 1
            print("OUTSIDE", L, a, b)
    print(f"{n} projections, {out} outside")


if __name__ == "__main__":
    main()
