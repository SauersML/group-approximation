"""Chunked, resumable driver for the ejection-arc machine check (imglayer.py of
experiments/h4-i25-image-layer-centres-2026-09-17) on ALL exact L=(1,1,1) constrained A_6 tuples.

Same tests (H), (P1), (P2), (P3) as imglayer.py; see its docstring.  Differences:
  * the tuple list is enumerated once and cached in tuples_L111.txt (index, word names);
  * `python3 imglayer_all.py START END` processes tuple indices [START, END) and appends one line per tuple
    to imglayer_all.log, so a run cut off by `timeout` loses at most one tuple.
Run: ARCS_N=7 PYTHONPATH=<prev experiment dir>:<curver>:<realalg> python3 imglayer_all.py START END"""
import os, sys, itertools
os.environ.setdefault('ARCS_N', '7')
HERE = os.path.dirname(os.path.abspath(__file__))
PREV = os.path.join(HERE, '..', 'h4-i25-image-layer-centres-2026-09-17')
sys.path.insert(0, PREV)
import a6
from a6 import mc, words, sig, inv, spider, xarc as cvx, adj, D, FG, NG
import arcs as AR
from search import outer

PC = 3
GV = [D] + [a6.A(i, j) for j in (5, 6, 7) for i in range(1, j)]
TUP = os.path.join(HERE, 'tuples_L111.txt')
LOG = os.path.join(HERE, 'imglayer_all.log')


def dcount(w):
    return sum(s for i, s in w if i == 0)


def enumerate_tuples():
    FA, N1 = words(FG, 1), words(NG, 1)
    lhs = {}
    for (wa1, a1), (wa2, a2) in itertools.product(FA, FA):
        for wb3, b3 in N1:
            lhs.setdefault(sig(inv(b3) + a1 + a2 + b3), []).append((wa1, wa2, wb3, b3))
    out = []
    for (wa1, a1), (wb1, b1), (wa2, a2) in itertools.product(FA, N1, FA):
        rhs = a1 + b1 + a2 + inv(b1)
        for (va1, va2, wb3, b3) in lhs.get(sig(rhs), []):
            if (va1, va2) != (wa1, wa2) or mc(inv(b3) + a1 + a2 + b3) != mc(rhs):
                continue
            if mc(a1 + a2).is_identity() or mc(inv(b1) + inv(b3)).is_identity():
                continue
            out.append((wa1, wb1, wa2, wb3))
    return out


def load_tuples():
    if os.path.exists(TUP):
        with open(TUP) as f:
            return [eval(l.split(' ', 1)[1]) for l in f if l.strip()]
    T = enumerate_tuples()
    with open(TUP, 'w') as f:
        for k, t in enumerate(T):
            f.write('%d %r\n' % (k, t))
    return T


def build(w, gens):
    b = []
    for i, s in w:
        b += gens[i] if s == 1 else inv(gens[i])
    return b


def test(t, M=4):
    wa1, wb1, wa2, wb3 = t
    a1, b1, a2, b3 = build(wa1, FG), build(wb1, NG), build(wa2, FG), build(wb3, NG)
    gx = [[], a1, a1 + b1 + a2]
    hy = {(0, 1): [], (1, 2): a1 + b1, (2, 0): inv(b3)}
    m = {(0, 1): 0, (1, 2): dcount(wb1), (2, 0): -dcount(wb3)}
    items = [(g, AR.xarc(g)) for g in gx]
    if any(it[1].end != ('P', 6) for it in items):
        return 'bad-arc', {}
    R = {p: outer([items[p[0]], items[p[1]]]) for p in hy}
    RX = outer(items)
    if RX is None or any(r is None for r in R.values()):
        return 'undetermined', {}
    res = {}
    res['H'] = all({0, 1, 2} <= r for r in R.values()) and {0, 1, 2} <= RX
    out = [p for p in hy if PC not in R[p]]
    ms = {m[p] for p in out}
    res['P1'] = len(ms) <= 1
    res['pc'] = 'in-R' if PC in RX else 'ejected'
    res['helly-pc'] = not (PC in RX and out)
    xs = [cvx(g) for g in gx]
    iscen = lambda b: all(adj(spider(b), x) for x in xs)
    tw = [j for j in range(-M, M + 1) if iscen(D * j if j >= 0 else inv(D) * (-j))]
    yc = [p for p in hy if iscen(hy[p])]
    res['tw'], res['yc'], res['m'] = tw, yc, m
    if PC not in RX:
        mm = min(ms) if ms else None
        res['P2'] = not (any(j != mm for j in tw) or any(m[p] != mm for p in yc))
    found = bool(tw or yc)
    if not found:
        Dk = {k: (D * k if k >= 0 else inv(D) * (-k)) for k in (-1, 0, 1)}
        for p in hy:
            for g in [[]] + GV + [inv(x) for x in GV]:
                if any(iscen(hy[p] + g + Dk[k]) for k in Dk):
                    found = True
                    break
            if found:
                break
    res['P3'] = found
    return 'determined', res


def main(start=0, end=None):
    assert AR.N == 7
    T = load_tuples()
    end = len(T) if end is None else min(end, len(T))
    done = set()
    if os.path.exists(LOG):
        with open(LOG) as f:
            done = {int(l.split()[0]) for l in f if l[:1].isdigit()}
    for k in range(start, end):
        if k in done:
            continue
        st, res = test(T[k])
        with open(LOG, 'a') as f:
            f.write('%d %s %r\n' % (k, st, res))


if __name__ == '__main__':
    a = [int(x) for x in sys.argv[1:]]
    main(*a)
