"""Calibrate the crossing-sign convention of mono.py against the curver model of a6.py:
rho_a(P_X) must fix the arc xi_0 = s_7 and rho_a(P_Y) must fix the spider delta_0 (as vertices:
P_Y-images fix delta_0 up to P_4567, i.e. the spider arcs are fixed)."""
import sys, os, random
B = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))
sys.path[:0] = [B + '/pkgs/curver-0.5.1', B + '/pkgs/realalg-0.3.7']
from mono import SH, read_braid, free_reduce, is_pure
import curver
S = curver.load(0, 10)
X0 = S.arcs['s_7']
LEGS = [S.arcs['s_0'], S('s_1')(S.arcs['s_0']), S('s_2.s_1')(S.arcs['s_0'])]


def mc(b):
    return S('.'.join(('s_%d' if g > 0 else 'S_%d') % abs(g) for g in b)) if b else S('')


def conj(g, w):
    return g + w + [-a for a in reversed(g)]


rng = random.Random(3)
PX, PY = [], []
for _ in range(12):
    g = [rng.choice([2, 3, 4, -2, -3, -4]) for _ in range(rng.randint(1, 5))]
    PX.append(conj(g, [rng.choice([2, 3, 4])] * 2))
    g = [rng.choice([1, 2, 3, -1, -2, -3]) for _ in range(rng.randint(1, 5))]
    PY.append(conj(g, [rng.choice([1, 2, 3])] * 2))
for sgn in (1, -1):
    bad = 0
    for sh in SH:
        for w in PX:
            b = [sgn * g for g in read_braid(sh, w)]
            bad += mc(b)(X0) != X0
        for w in PY:
            b = [sgn * g for g in read_braid(sh, w)]
            h = mc(b)
            bad += any(h(l) != l for l in LEGS)
    print('sign', sgn, 'violations', bad, 'of', 3 * (len(PX) + len(PY)))
