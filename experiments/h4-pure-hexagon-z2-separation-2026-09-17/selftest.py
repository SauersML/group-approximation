"""Cross-check arcs.py against curver: for random braids, the crossing counts of the placed chord diagram must
equal curver's geometric intersection numbers (so the placement is pairwise minimal and the Artin-action
convention matches curver's half-twists), for x/x, x/y and y/y pairs.
curver model: S_{0,7}, punctures e1,q,a,b,t,e0,inf = 0..6; x-arcs g(s_4), y-arcs g(s_0); s_1,s_2,s_3 = sigma_1..3.
Run: PYTHONPATH=<curver>:<realalg> python3 selftest.py [trials] [len]"""
import random, sys
import curver
from arcs import xarc, yarc, Placement, tight

from arcs import N
S = curver.load(0, N + 3)
X0, Y0 = S.arcs["s_%d" % N], S.arcs["s_0"]


def cv(braid):
    return S('.'.join(('s_%d' if g > 0 else 'S_%d') % abs(g) for g in braid)) if braid else S('')


def run(trials=300, L=6, seed=1):
    rng = random.Random(seed)
    bad = 0
    for _ in range(trials):
        bs = [[rng.choice([g for g in range(-N + 1, N) if g]) for _ in range(rng.randint(0, L))] for _ in range(4)]
        kinds = ['x', 'x', 'y', 'x']
        arcs = [xarc(b) if k == 'x' else yarc(b) for b, k in zip(bs, kinds)]
        P = tight(arcs)
        if P is None:
            bad += 1; print('NO TIGHT PLACEMENT', bs); continue
        cnt = P.crossings()
        cvarcs = [cv(b)(X0 if k == 'x' else Y0) for b, k in zip(bs, kinds)]
        for i in range(4):
            if cnt.get((i, i), 0):
                bad += 1; print('self-crossing', i, bs[i], arcs[i].word)
            for j in range(i + 1, 4):
                if (arcs[i].word, arcs[i].end, arcs[i].start) == (arcs[j].word, arcs[j].end, arcs[j].start):
                    continue
                c1 = cnt.get((i, j), 0)
                c2 = cvarcs[i].intersection(cvarcs[j])
                if c1 != c2:
                    bad += 1
                    print('MISMATCH', kinds[i], kinds[j], bs[i], bs[j], arcs[i].word, arcs[j].word, c1, c2)
    print('trials', trials, 'mismatches', bad)
    return bad


if __name__ == '__main__':
    run(int(sys.argv[1]) if len(sys.argv) > 1 else 300, int(sys.argv[2]) if len(sys.argv) > 2 else 6)
