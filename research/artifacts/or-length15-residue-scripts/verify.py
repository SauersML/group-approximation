#!/usr/bin/env python3
"""Independent check of vfib.py CERT lines.

A CERT line names a transitive permutation representation (a, t) of G = <a,t | w> of
degree k (a subgroup H of index k), a cocycle c on the covering complex X_H, vertex
potentials pot, and cp = c + delta(pot).  This script rebuilds everything from w, a, t, cp:
  1. a and t are permutations, w acts trivially, the action is transitive;
  2. cp - c is the coboundary of pot, cp sums to zero around every cell lift, and the
     loop values of cp have gcd 1 (the cyclic cover along phi is connected);
  3. with S the largest height span of a cell, the explicit finite complexes
     X[0,S+1] and X[-1,S] of the infinite cyclic cover collapse elementarily onto X[0,S]
     (every piece of the extra level is removed via a free face, recounted from scratch);
  4. the fibre rank 1 - chi(X[0,S]) equals deg delta, and delta has unit end coefficients.
Step 3 makes the infinite cyclic cover deformation retract onto X[0,S], so ker phi is
finitely presented; by Bieri's theorem (cd H = 2) it is free, and H is free-by-cyclic.
Usage: verify.py FILE...   (reads lines starting with CERT)
"""
import sys, re, ast, random
from math import gcd

def parse(line):
    tok = line.split()
    F = {key: ast.literal_eval(val) for key, val in re.findall(r' (\w+)=(\[[^\]]*\])', line)}
    return tok[1], int(tok[2][2:]), F

def window(w, a, t, cp, lo, hi):
    """Pieces of the full subcomplex of the infinite cyclic cover on heights [lo, hi]."""
    k = len(a)
    perm = {'a': a, 't': t}
    inv = {g: [p.index(i) for i in range(k)] for g, p in perm.items()}
    ecp = lambda g, i: cp[(0 if g == 'a' else k) + i]
    cells = []
    for s0 in range(k):
        j, h, occ, hs = s0, 0, [], [0]
        for ch in w:
            g = ch.lower()
            if ch.islower():
                occ.append((g, j, h)); h += ecp(g, j); j = perm[g][j]
            else:
                j = inv[g][j]; h -= ecp(g, j); occ.append((g, j, h))
            hs.append(h)
        if j != s0 or h != 0:
            return None
        cells.append((occ, min(hs), max(hs)))
    V = [('v', v, x) for v in range(k) for x in range(lo, hi + 1)]
    E, C, bd = [], [], {}
    for g in 'at':
        for i in range(k):
            c = ecp(g, i)
            for x in range(lo, hi + 1):
                if lo <= x + c <= hi:
                    E.append(('e', g, i, x)); bd[E[-1]] = [('v', i, x), ('v', perm[g][i], x + c)]
    for ci, (occ, mn, mx) in enumerate(cells):
        for x in range(lo - mn, hi - mx + 1):
            C.append(('c', ci, x)); bd[C[-1]] = [('e', g, i, y + x) for (g, i, y) in occ]
    span = max(mx - mn for _, mn, mx in cells)
    return V, E, C, bd, span

def collapses(big, small, rng, tries=20):
    V, E, C, bd, _ = big
    target = set(small[0]) | set(small[1]) | set(small[2])
    for _ in range(tries):
        alive = set(V) | set(E) | set(C)
        while True:
            extra = [p for p in alive if p not in target]
            if not extra:
                return True
            moves = []
            for f in extra:
                if f[0] == 'c':
                    continue
                cof = [(q, bd[q].count(f)) for q in alive if q[0] != 'v' and f in bd[q]]
                if len(cof) == 1 and cof[0][1] == 1 and cof[0][0] not in target:
                    moves.append((f, cof[0][0]))
            if not moves:
                break
            f, q = rng.choice(moves)
            alive.discard(f); alive.discard(q)
    return False

def verify(line):
    s, k, F = parse(line)
    a, t, c, pot, cp, delta = F['a'], F['t'], F['c'], F['pot'], F['cp'], F['delta']
    if sorted(a) != list(range(k)) or sorted(t) != list(range(k)):
        return 'FAIL perm'
    perm = {'a': a, 't': t}
    inv = {g: [p.index(i) for i in range(k)] for g, p in perm.items()}
    for i in range(k):
        j = i
        for ch in s:
            j = perm[ch][j] if ch.islower() else inv[ch.lower()][j]
        if j != i:
            return 'FAIL relator'
    seen, st = {0}, [0]
    while st:
        i = st.pop()
        for j in (a[i], t[i], inv['a'][i], inv['t'][i]):
            if j not in seen:
                seen.add(j); st.append(j)
    if len(seen) != k:
        return 'FAIL transitive'
    ends = [(i, a[i]) for i in range(k)] + [(i, t[i]) for i in range(k)]
    if any(cp[e] != c[e] + pot[v] - pot[u] for e, (u, v) in enumerate(ends)):
        return 'FAIL coboundary'
    hv, st, g = {0: 0}, [0], 0
    adj = [[] for _ in range(k)]
    for e, (u, v) in enumerate(ends):
        adj[u].append((v, cp[e])); adj[v].append((u, -cp[e]))
    while st:
        u = st.pop()
        for v, d in adj[u]:
            if v not in hv:
                hv[v] = hv[u] + d; st.append(v)
    for e, (u, v) in enumerate(ends):
        g = gcd(g, abs(hv[u] + cp[e] - hv[v]))
    if g != 1:
        return 'FAIL primitive gcd=%d' % g
    base = window(s, a, t, cp, 0, 0)
    if base is None:
        return 'FAIL cocycle'
    S = base[4]
    mid = window(s, a, t, cp, 0, S)
    rng = random.Random(7)
    if not collapses(window(s, a, t, cp, 0, S + 1), mid, rng):
        return 'FAIL top-collapse'
    if not collapses(window(s, a, t, cp, -1, S), mid, rng):
        return 'FAIL bottom-collapse'
    n = 1 - (len(mid[0]) - len(mid[1]) + len(mid[2]))
    if n != len(delta) - 1 or abs(delta[0]) != 1 or abs(delta[-1]) != 1:
        return 'FAIL rank n=%d deg=%d' % (n, len(delta) - 1)
    return 'VERIFIED k=%d S=%d fibre=F_%d' % (k, S, n)

def main():
    for path in sys.argv[1:]:
        for line in open(path):
            if line.startswith('CERT'):
                print('%s %s' % (line.split()[1], verify(line)), flush=True)
    print('SENTINEL_DONE', flush=True)

if __name__ == '__main__':
    main()
