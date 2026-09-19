#!/usr/bin/env python3
"""wallsearch.py -- exact search for general window walls in the scale-D presentation (lane bh-g2-labbe, 2026-09-18).

For a window K (rectangle containing 0 and v) and interior-box legality (the relations of the window algebra C_D(K)),
a WALL is a pair x, y of K-patterns (every s x s box inside K legal) whose difference set puts 0 and v in different
2D-components (sup-steps <= 2D), with x(0) != y(0) and x(v) != y(v).  A wall is a 2-dim representation of C_D(K) with
[P_0, P_v] != 0 (node contextual-closure-certifies-quantum-rigidity, item 3), so NO certificate supported in K exists.

Exact reduction used: walls  <=>  chains y - z - x of K-patterns with
    y = z on N_v = B_2D(v) ∩ K,  y(0) != z(0);   x = z on N_0 = B_2D(0) ∩ K,  x(v) != z(v);
    dist_inf(Delta(y,z), Delta(z,x)) > 2D.
(=>: z = x on the 0-component A of Delta(x,y), y elsewhere, is legal since no box meets A and Delta(x,y) \\ A.)
Counts reported: patterns z admitting a wall.  Controls: certified offsets must give 0.
Usage: python3 wallsearch.py [--smoke]
"""
import sys, time
from collections import defaultdict
import j2probe as J

def log(*a): print('[%7.1fs]' % J.el(), *a, flush=True)

def window_walls(Lbox, s, v, mx, my, cap):
    R = s - 1
    x0 = min(0, v[0]) - mx; x1 = max(0, v[0]) + mx
    y0 = min(0, v[1]) - my; y1 = max(0, v[1]) + my
    w, h = x1 - x0 + 1, y1 - y0 + 1
    if w < s or h < s: return None
    pats = None
    for hh, level in J.local_levels(Lbox, s, w, h, cap, J.BUDGET):
        if hh == h: pats = level
    if pats is None: return ('cap', w, h)
    n = w * h
    co = [(i % w + x0, i // w + y0) for i in range(n)]
    ix = lambda x, y: (y - y0) * w + (x - x0)
    i0, iv = ix(0, 0), ix(v[0], v[1])
    N0 = [i for i in range(n) if max(abs(co[i][0]), abs(co[i][1])) <= R]
    Nv = [i for i in range(n) if max(abs(co[i][0] - v[0]), abs(co[i][1] - v[1])) <= R]
    dil = []
    for i in range(n):
        m = 0
        for j in range(n):
            if max(abs(co[i][0] - co[j][0]), abs(co[i][1] - co[j][1])) <= R: m |= 1 << j
        dil.append(m)
    flat = [tuple(c for row in P for c in row) for P in pats]
    gv = defaultdict(list); g0 = defaultdict(list)
    for k, X in enumerate(flat):
        gv[tuple(X[i] for i in Nv)].append(k); g0[tuple(X[i] for i in N0)].append(k)
    def dmask(X, Y):
        m = 0
        for i in range(n):
            if X[i] != Y[i]: m |= 1 << i
        return m
    nz = 0; ex = None
    for k, Z in enumerate(flat):
        As = [dmask(flat[j], Z) for j in gv[tuple(Z[i] for i in Nv)] if flat[j][i0] != Z[i0]]
        if not As: continue
        Bs = [dmask(flat[j], Z) for j in g0[tuple(Z[i] for i in N0)] if flat[j][iv] != Z[iv]]
        if not Bs: continue
        hit = False
        for A in As:
            dA = 0; m = A
            while m:
                low = m & -m; dA |= dil[low.bit_length() - 1]; m ^= low
            for B in Bs:
                if dA & B == 0:
                    hit = True
                    if ex is None:
                        ex = (sorted(co[i] for i in range(n) if A >> i & 1), sorted(co[i] for i in range(n) if B >> i & 1))
                    break
            if hit: break
        if hit: nz += 1
    return (w, h, len(pats), nz, ex)

def run(tag, v, margins, cap):
    LAB5 = J.labbe_windows(5, 5)
    for (mx, my) in margins:
        if J.el() > J.BUDGET: log('time budget'); return
        r = window_walls(LAB5, 5, v, mx, my, cap)
        if r is None: continue
        if r[0] == 'cap': log('WALLS %s v=%s margins=(%d,%d) window %dx%d: over cap' % (tag, v, mx, my, r[1], r[2])); return
        w, h, N, nz, ex = r
        exs = ''
        if ex: exs = '  e.g. |A|=%d near 0 %s ; |B|=%d near v %s' % (len(ex[0]), ex[0][:6], len(ex[1]), ex[1][:6])
        log('WALLS %s v=%s margins=(%d,%d) window %dx%d patterns=%d wall-carrying z=%d%s' % (tag, v, mx, my, w, h, N, nz, exs))

if __name__ == '__main__':
    smoke = '--smoke' in sys.argv
    cap = 20000 if smoke else 300000
    ms = [(0, 0), (1, 1)] if smoke else [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4)]
    log('controls (certified offsets must give 0 walls once the window contains their certificate)')
    run('control', (5, 0), [(0, 2), (1, 3)] if smoke else [(0, 2), (0, 4), (1, 3), (2, 4), (0, 6)], cap)
    run('control', (-5, -2), [(0, 1), (1, 2)] if smoke else [(0, 1), (1, 2), (2, 3), (3, 4)], cap)
    log('resonant axis offset (6,0): compare band walls 7,5,3,1,0 at H=2..6')
    run('axis6', (6, 0), [(0, 2), (0, 3)] if smoke else [(0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 6)], cap)
    log('frontier offsets at distance 5')
    for v in [(5, 5), (5, -5), (5, 4), (4, 5), (5, -4), (4, -5), (-3, 5)]:
        run('frontier', v, ms, cap)
    log('DONE')
