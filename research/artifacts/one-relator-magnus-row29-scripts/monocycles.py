#!/usr/bin/env python3
"""Folded Stallings graphs of the row-29 edge groups: edge lists, monochromatic cycles, membership.

A folded graph gives a partial injection per letter, so every monochromatic component is a path or
a cycle. A cycle of letter l through vertex p with tree word alpha (0 -> p) gives
alpha l^k alpha^-1 in the subgroup, where k is the cycle length. Every conjugate of a power of l
lying in the subgroup arises this way. Membership: reading a reduced word from 0 must stay defined
and end at 0.
Usage: monocycles.py NAME 'gens comma-separated' [NAME 'gens'] ... -- WORD...
"""
import sys
from algext import stallings

def succ(E, l):
    return {u: v for (u, lab, v) in E if lab == l}

def monocycles(nv, E):
    out = []
    for l in 'xy':
        s, seen = succ(E, l), set()
        for start in range(nv):
            if start in seen or start not in s:
                continue
            path, u = [], start
            while u in s and u not in path:
                path.append(u); u = s[u]
            if u == start:
                out.append((l, len(path), list(path)))
            seen.update(path)
    return out

def member(E, w):
    fwd = {(u, lab): v for (u, lab, v) in E}
    bwd = {(v, lab): u for (u, lab, v) in E}
    u = 0
    for ch in w:
        key = (u, ch.lower())
        nxt = fwd.get(key) if ch.islower() else bwd.get(key)
        if nxt is None:
            return False
        u = nxt
    return u == 0

args = sys.argv[1:]
sep = args.index('--')
pairs, words = args[:sep], args[sep + 1:]
for i in range(0, len(pairs), 2):
    name, gens = pairs[i], pairs[i + 1].split(',')
    nv, E = stallings(gens)
    print('== %s = <%s>: V=%d E=%d rank=%d' % (name, ','.join(gens), nv, len(E), len(E) - nv + 1))
    print('EDGES %s' % sorted(E))
    for l, k, path in monocycles(nv, E):
        print('MONOCYCLE %s letter=%s length=%d vertices=%s' % (name, l, k, path))
    for w in words:
        print('MEMBER %s %s %s' % (name, w, member(E, w)))
print('SENTINEL_DONE')
