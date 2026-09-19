#!/usr/bin/env python3
"""Hanoi even-step decidability from bounded labels: label = disk size mod M at each top
(plus n mod 2 and the last-moved mark).  Conflicts = same bounded data, different correct move."""
import collections, sys
sys.setrecursionlimit(10000)


def solve(n):
    moves = []

    def rec(k, s, d, v):
        if k:
            rec(k - 1, s, v, d); moves.append((k, s, d)); rec(k - 1, v, d, s)
    rec(n, 0, 2, 1)
    return moves


for M in (2, 3, 4, 5, 6, 8, 12, 16):
    table = collections.defaultdict(set)
    for n in range(3, 16):
        pegs = [list(range(n, 0, -1)), [], []]
        last = None
        for k, s, d in solve(n):
            if k != 1:
                r = next(p for p in range(3) if pegs[p] and pegs[p][-1] == 1)
                a, b = (r + 1) % 3, (r + 2) % 3
                ta = pegs[a][-1] if pegs[a] else None
                tb = pegs[b][-1] if pegs[b] else None
                key = (n % 2, None if ta is None else ta % M, None if tb is None else tb % M,
                       ta == last, tb == last)
                table[key].add('a->b' if (s, d) == (a, b) else 'b->a')
                last = k
            pegs[d].append(pegs[s].pop())
    conf = sum(1 for v in table.values() if len(v) > 1)
    print(f'labels size mod {M:2d}: keys {len(table):4d}  conflicting {conf}')
