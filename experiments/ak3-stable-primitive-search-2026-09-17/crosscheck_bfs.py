#!/usr/bin/env python3
"""crosscheck_bfs.py -- independent Python re-count of the pzsearch component sizes.

usage: crosscheck_bfs.py CAP [r1 r2]      (rank 3, default AK(3) = xxxYYYY xyxYXY)

Uses the move code of verify_chain.py (a separate implementation from pzsearch.c) and closes the
component of the start under M1/M2, restricted to total length <= CAP and nonempty relators.
States are counted up to rotation, inversion, order and signed permutations (every symmetric
image is marked visited when a state is inserted).  Prints the state count and whether any
state has a primitive relator.
"""
import sys
from verify_chain import neighbours, signed_perms, subst, pform, is_primitive

RANK = 3
PERMS = list(signed_perms(RANK))


def main():
    cap = int(sys.argv[1])
    r1, r2 = (sys.argv[2], sys.argv[3]) if len(sys.argv) > 3 else ("xxxYYYY", "xyxYXY")
    seen = set()
    queue = []

    def add(p, q):
        if pform(p, q) in seen:
            return
        for s in PERMS:
            seen.add(pform(subst(p, s), subst(q, s)))
        queue.append(pform(p, q))

    add(r1, r2)
    head = 0
    goal = False
    while head < len(queue):
        p, q = queue[head]
        head += 1
        if is_primitive(p, RANK, []) or is_primitive(q, RANK, []):
            goal = True
            print("GOAL", p, q)
            break
        for (a, b) in neighbours(p, q, RANK):
            if a and b and len(a) + len(b) <= cap:
                add(a, b)
    print(f"CAP {cap} states {len(queue)} goal {goal}")


if __name__ == "__main__":
    main()
