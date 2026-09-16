#!/usr/bin/env python3
"""Checks behind the 1-block factor Omega_U -> S_alpha x S_alpha (artifact
research/artifacts/labbe-sturmian-product-factor-2026-09-16.md, Section 2).

Reads partitionU_data.txt (produced by extract_figure.py from Labbe's e-print).
Checks, all printed with PASS/FAIL:
 C1  the four circles x1 = 0, x1 = alpha, x2 = 0, x2 = 1 - alpha (alpha = phi^-2) are unions of drawn
     segments (on the closed square, frame lines counted on both sides);
 C2  the complement of the drawn segments in the open square has exactly 19 faces, each face contains
     exactly one label, and the labels are 0..18 (raster flood fill, 4-connectivity);
 C3  each face lies in one cell of the grid {x1 < alpha, x1 > alpha} x {x2 < 1-alpha, x2 > 1-alpha};
     this defines pi1(u) = [face of u has x1 < alpha] and pi2(u) = [face of u has x2 > 1-alpha];
 C4  (independent of the figure) on every colour-matching VERTICAL domino (top(a) = bottom(b)),
     pi1(a) = pi1(b); on every colour-matching HORIZONTAL domino (right(a) = left(b)), pi2(a) = pi2(b);
 C5  no colour-matching horizontal domino has pi1 = (1,1), no vertical domino has pi2 = (1,1)
     (Sturmian words of slope phi^-2 < 1/2 have isolated 1s);
 C6  raster areas: total area of atoms with pi1 = 1 is ~alpha, with pi2 = 1 is ~alpha.
Also prints, for information, the labels on the two sides of the off-frame segments
sigma_v = (phi^-2,0)-(phi^-2,phi^-2) and sigma_h = (phi^-3,phi^-1)-(phi^-2,phi^-1).
"""
import math
import sys
from collections import deque

FR = 85.04042
PHI = (1 + 5 ** 0.5) / 2
ALPHA = PHI ** -2
N = 1024  # raster cells per side


def load(path):
    segs, labels, tiles = [], {}, {}
    for line in open(path):
        w = line.split()
        if not w:
            continue
        if w[0] == 'SEG':
            segs.append(tuple(float(v) / FR for v in w[1:5]))
        elif w[0] == 'LABEL':
            labels[int(w[1])] = (float(w[2]) / FR, float(w[3]) / FR)
        elif w[0] == 'TILE':
            tiles[int(w[1])] = tuple(w[2:6])  # right, top, left, bottom
    return segs, labels, tiles


def report(name, ok, extra=''):
    print('%s %s %s' % (name, 'PASS' if ok else 'FAIL', extra))
    return ok


def covered(segs, axis, c, eps=1e-4):
    """Union of the parameter intervals of segments lying on the line {coord[axis] = c}."""
    ivs = []
    for (x0, y0, x1, y1) in segs:
        p0, p1 = (x0, y0), (x1, y1)
        if abs(p0[axis] - c) < eps and abs(p1[axis] - c) < eps:
            o = 1 - axis
            ivs.append((min(p0[o], p1[o]), max(p0[o], p1[o])))
    ivs.sort()
    reach = 0.0
    for a, b in ivs:
        if a > reach + eps:
            return False, ivs
        reach = max(reach, b)
    return reach > 1 - eps, ivs


def main():
    segs, labels, tiles = load(sys.argv[1] if len(sys.argv) > 1 else 'partitionU_data.txt')
    allok = True
    # C1: circles; on the torus x=0 and x=1 are the same circle, so either copy suffices
    for axis, c, name in [(0, 0.0, 'x1=0'), (0, ALPHA, 'x1=alpha'), (1, 0.0, 'x2=0'), (1, 1 - ALPHA, 'x2=1-alpha')]:
        ok, ivs = covered(segs, axis, c)
        if not ok and c == 0.0:
            ok, ivs = covered(segs, axis, 1.0)
        allok &= report('C1 circle %s covered' % name, ok, str([(round(a, 4), round(b, 4)) for a, b in ivs]))
    # raster
    wall = bytearray(N * N)
    for (x0, y0, x1, y1) in segs:
        L = math.hypot(x1 - x0, y1 - y0)
        steps = int(L * N * 4) + 2
        for k in range(steps + 1):
            t = k / steps
            i = min(N - 1, int((x0 + t * (x1 - x0)) * N))
            j = min(N - 1, int((y0 + t * (y1 - y0)) * N))
            wall[j * N + i] = 1
    comp = [-1] * (N * N)
    faces = []  # list of (cells count, minx, maxx, miny, maxy)
    for start in range(N * N):
        if wall[start] or comp[start] != -1:
            continue
        cid = len(faces)
        q = deque([start])
        comp[start] = cid
        cnt, mnx, mxx, mny, mxy = 0, N, -1, N, -1
        while q:
            c = q.popleft()
            cnt += 1
            j, i = divmod(c, N)
            mnx, mxx, mny, mxy = min(mnx, i), max(mxx, i), min(mny, j), max(mxy, j)
            for d, okd in ((c - 1, i > 0), (c + 1, i < N - 1), (c - N, j > 0), (c + N, j < N - 1)):
                if okd and not wall[d] and comp[d] == -1:
                    comp[d] = cid
                    q.append(d)
        faces.append((cnt, mnx / N, (mxx + 1) / N, mny / N, (mxy + 1) / N))
    big = [f for f in range(len(faces)) if faces[f][0] > 20]  # ignore raster slivers at segment junctions

    def face_at(x, y):
        return comp[int(y * N) * N + int(x * N)]

    # label box origin (baseline left); try two interior sample points per label
    face_of = {}
    consistent = True
    for u, (x, y) in labels.items():
        fs = {face_at(x + 5.0 / FR, y + 1.5 / FR), face_at(x + 3.0 / FR, y + 2.5 / FR)}
        fs.discard(-1)
        if len(fs) != 1:
            consistent = False
        face_of[u] = fs.pop() if fs else -1
    labelled = sorted(face_of.values())
    ok = (consistent and len(big) == 19 and sorted(face_of) == list(range(19))
          and len(set(labelled)) == 19 and set(labelled) == set(big))
    allok &= report('C2 19 faces, one label each', ok, 'faces(>20 cells)=%d labels=%d' % (len(big), len(labels)))
    tol = 2.0 / N
    pi1, pi2 = {}, {}
    ok3 = True
    for u, f in face_of.items():
        _, a, b, c, d = faces[f]
        if b <= ALPHA + tol:
            pi1[u] = 1
        elif a >= ALPHA - tol:
            pi1[u] = 0
        else:
            ok3 = False
        if c >= 1 - ALPHA - tol:
            pi2[u] = 1
        elif d <= 1 - ALPHA + tol:
            pi2[u] = 0
        else:
            ok3 = False
    allok &= report('C3 every face inside one grid cell', ok3,
                    'pi1=1: %s ; pi2=1: %s' % (sorted(u for u in pi1 if pi1[u]), sorted(u for u in pi2 if pi2[u])))
    # C4, C5 on colour-matching dominoes
    vert = [(a, b) for a in tiles for b in tiles if tiles[a][1] == tiles[b][3]]
    hor = [(a, b) for a in tiles for b in tiles if tiles[a][0] == tiles[b][2]]
    ok4 = all(pi1[a] == pi1[b] for a, b in vert) and all(pi2[a] == pi2[b] for a, b in hor)
    allok &= report('C4 pi1 constant on vertical dominoes, pi2 on horizontal', ok4,
                    'vertical=%d horizontal=%d' % (len(vert), len(hor)))
    ok5 = all(not (pi1[a] and pi1[b]) for a, b in hor) and all(not (pi2[a] and pi2[b]) for a, b in vert)
    allok &= report('C5 no 11 in pi1 along rows or pi2 along columns', ok5)
    area1 = sum(faces[face_of[u]][0] for u in pi1 if pi1[u]) / (N * N)
    area2 = sum(faces[face_of[u]][0] for u in pi2 if pi2[u]) / (N * N)
    ok6 = abs(area1 - ALPHA) < 0.01 and abs(area2 - ALPHA) < 0.01
    allok &= report('C6 strip areas ~ alpha', ok6, 'area(pi1=1)=%.4f area(pi2=1)=%.4f alpha=%.4f' % (area1, area2, ALPHA))
    # informational: sides of sigma_v and sigma_h
    inv = {f: u for u, f in face_of.items()}
    e = 3.0 / N
    for name, pts in [('sigma_v', [(ALPHA - e, t * ALPHA, ALPHA + e, t * ALPHA) for t in (0.2, 0.5, 0.8)]),
                      ('sigma_h', [(PHI ** -3 + t * PHI ** -4, 1 - ALPHA - e, PHI ** -3 + t * PHI ** -4, 1 - ALPHA + e)
                                   for t in (0.2, 0.5, 0.8)])]:
        sides = [(inv.get(face_at(a, b)), inv.get(face_at(c, d))) for a, b, c, d in pts]
        print('INFO %s (side-, side+) labels at 3 sample points: %s' % (name, sides))
    print('ALL', 'PASS' if allok else 'FAIL')
    return 0 if allok else 1


if __name__ == '__main__':
    sys.exit(main())
