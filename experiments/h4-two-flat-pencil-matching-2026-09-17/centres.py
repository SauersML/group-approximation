"""Pinned classes and joint centres of doubly ejected genuine Case 1 tuples (records of joint.py).

For a tuple and a pair of shadows (V_a, V_b) in which p_{a+1} is ejected in V_a and p_{b+1} in V_b:
  * candidates g = u_P . w, P a hexagon pair (u_12 = 1, u_23 = a1 b1, u_31 = b3^-1), w = 1 or m^{+-1} or
    m^{+-1} m'^{+-1} for m, m' among the 15 meridians of A_x (genuine H_4 words);
  * g is a centre in V_a iff the spider rho_a(g)(legs) is disjoint from the three x-arcs (curver);
  * its class: the H_1(M(A)) coordinates of g on the four P_Z-invariant lines of Pi_ab, namely the two core walls
    (o14, p_{a+1}), (o14, p_{b+1}) and the two extra walls {eps, eps'} (x2,x3 / x5,x11 / x6,x10).  These are
    coordinates of the genuine element, so they equal the linking numbers in either shadow.
Reports, per (tuple, a, b): the class sets L_a, L_b of the centres found in V_a, V_b, and the joint centres.
Run: PYTHONPATH=<curver>:<realalg> python3 centres.py records.jsonl [maxlen_w]"""
import os, sys, json, itertools, pickle
from collections import Counter
import numpy as np
from joint import FGEN, NGEN, inv, HERE
sys.path.insert(0, os.path.join(HERE, '..', '..', 'lib'))
import a6
from mono import SIM, SMAT, W, idx, name
import gens

LINES = {(0, 1): ('x0', 'x1', 'x2', 'x3'), (0, 2): ('x0', 'x4', 'x5', 'x11'), (1, 2): ('x1', 'x4', 'x6', 'x10')}
WALL = {name(k): k for k in range(len(W))}
_C = os.path.join(HERE, 'mx_cache.pkl')
if os.path.exists(_C):
    MXG = pickle.load(open(_C, 'rb'))
else:
    MXG = [(name(k), w, [gens.free_reduce(gens.rho(a, w)) for a in range(3)]) for k, w in sorted(gens.MX.items())]
    pickle.dump(MXG, open(_C, 'wb'))
BYNAME = {g[0]: g for g in FGEN + NGEN}


def h1(word):
    """H_1(M(A)) class of a pure H_4 word: dict wall index -> coefficient."""
    Wm = np.eye(4); c = Counter()
    for g in word:
        i = abs(g) - 1
        c[idx(Wm @ SIM[i])] += (1 if g > 0 else -1)
        Wm = Wm @ SMAT[i]
    assert all(v % 2 == 0 for v in c.values())
    return {k: v // 2 for k, v in c.items() if v}


def parse(s):
    h, im = [], [[], [], []]
    for t in s.split():
        g = BYNAME[t.rstrip("'")]
        e = -1 if t.endswith("'") else 1
        h += g[1] if e == 1 else inv(g[1])
        for a in range(3):
            im[a] += g[2][a] if e == 1 else inv(g[2][a])
    return h, im


def cat(*xs):
    h, im = [], [[], [], []]
    for x in xs:
        h += x[0]
        for a in range(3):
            im[a] += x[1][a]
    return h, im


def xinv(x):
    return inv(x[0]), [inv(i) for i in x[1]]


def extras(L):
    ms = [(w, im) for _, w, im in MXG]
    ms = ms + [xinv(m) for m in ms]
    out = [([], [[], [], []])]
    if L >= 1:
        out += ms
    if L >= 2:
        out += [cat(m, n) for m in ms for n in ms]
    return out


def analyse(rec, L=1):
    a1, b1, a2, b3 = (parse(rec[k]) for k in ('a1', 'b1', 'a2', 'b3'))
    gx = [([], [[], [], []]), a1, cat(a1, b1, a2)]
    U = {'12': ([], [[], [], []]), '23': cat(a1, b1), '31': xinv(b3)}
    res = {}
    for ab, kv in rec.get('pairs', {}).items():
        kind = kv[0]
        a, b = int(ab[0]), int(ab[1])
        xs = {s: [a6.xarc(g[1][s]) for g in gx] for s in (a, b)}
        cen = lambda g, s: all(a6.adj(a6.spider(g[1][s]), x) for x in xs[s])
        La, Lb, joint = Counter(), Counter(), 0
        for P, u in U.items():
            for w in extras(L):
                g = cat(u, w)
                ca, cb = cen(g, a), cen(g, b)
                if not (ca or cb):
                    continue
                c = h1(g[0]); key = tuple(c.get(WALL[l], 0) for l in LINES[(a, b)])
                if ca:
                    La[key] += 1
                if cb:
                    Lb[key] += 1
                joint += ca and cb
        res[ab] = {'kind': kind, 'La': sorted(La), 'Lb': sorted(Lb), 'joint': joint,
                   'meet': sorted(set(La) & set(Lb))}
    return res


def main(path, L=1):
    st = Counter()
    for line in open(path):
        rec = json.loads(line)
        if not rec.get('pairs'):
            continue
        for ab, r in analyse(rec, L).items():
            st[(ab, r['kind'], 'joint' if r['joint'] else 'NOJOINT', 'meet' if r['meet'] else 'NOMEET',
                'La%d' % len(r['La']), 'Lb%d' % len(r['Lb']))] += 1
            if not r['joint'] or not r['meet']:
                print('CAND', ab, rec['a1'], '|', rec['b1'], '|', rec['a2'], '|', rec['b3'], r, flush=True)
    for k, v in sorted(st.items()):
        print(' ', k, v)


if __name__ == '__main__':
    main(sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else 1)
