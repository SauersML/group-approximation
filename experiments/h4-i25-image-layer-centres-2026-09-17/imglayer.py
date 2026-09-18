"""Machine check of the ejection-arc theorem (h4-i25-shadow-hexagons-have-image-layer-centres) on exact
constrained A_6 hexagons of the V0 shadow (cluster C = {1,2,3,4}, p_c = strand 4 = arcs.py puncture 3).

For each exact tuple (a6.py solver) with x-braids g1 = 1, g2 = a1, g3 = a1 b1 a2 and y-braids
h12 = 1, h23 = a1 b1, h31 = b3^-1, the twist exponents are m12 = 0, m23 = #D(b1), m31 = -#D(b3)
(f(h) = D^m on C, since F''-letters and A_{j5}, A_{j6} restrict trivially to C).
Regions R_ij = punctures of the d1-region of x_i u x_j, R = region of x1 u x2 u x3 (arcs.py placement, matched
to curver intersection numbers).  Tested predictions of the theorem:
  (H)  {1,2,3} (punctures 0,1,2) lie in every R_ij and in R            [Z/2 Helly, calibration]
  (P1) the m_ij over the pairs with p_c not in R_ij are all equal (= m)
  (P2) if p_c not in R: every twist centre D^j.spider0 has j = m, and every hexagon vertex y_ij that is a
       centre has m_ij = m
  (P3) some explicit centre lies in G_V.A_Y'': searched among the y_ij, the D^j.spider0 (|j| <= M) and
       h_ij . g . D^k . spider0 for g a G_V generator^{+-1} or 1, |k| <= 1.
Run: ARCS_N=7 PYTHONPATH=.:<curver>:<realalg> python3 imglayer.py [LF] [LN1] [LN3] [M]"""
import os, sys, itertools
from collections import Counter
os.environ.setdefault('ARCS_N', '7')
import a6
from a6 import mc, words, sig, inv, spider, xarc as cvx, adj, D, FG, NG
import arcs as AR
from search import outer

PC = 3
GV = [D] + [a6.A(i, j) for j in (5, 6, 7) for i in range(1, j)]


def dcount(w, gens_word):
    return sum(s for i, s in w if i == 0)


def main(LF=1, LN1=1, LN3=1, M=4):
    assert AR.N == 7
    FA, N1, N3 = words(FG, LF), words(NG, LN1), words(NG, LN3)
    lhs = {}
    for (wa1, a1), (wa2, a2) in itertools.product(FA, FA):
        for wb3, b3 in N3:
            lhs.setdefault(sig(inv(b3) + a1 + a2 + b3), []).append((wa1, wa2, wb3, b3))
    stat = Counter()
    for (wa1, a1), (wb1, b1), (wa2, a2) in itertools.product(FA, N1, FA):
        rhs = a1 + b1 + a2 + inv(b1)
        for (va1, va2, wb3, b3) in lhs.get(sig(rhs), []):
            if (va1, va2) != (wa1, wa2) or mc(inv(b3) + a1 + a2 + b3) != mc(rhs):
                continue
            if mc(a1 + a2).is_identity() or mc(inv(b1) + inv(b3)).is_identity():
                continue
            stat['tuples'] += 1
            gx = [[], a1, a1 + b1 + a2]
            hy = {(0, 1): [], (1, 2): a1 + b1, (2, 0): inv(b3)}
            m = {(0, 1): 0, (1, 2): dcount(wb1, NG), (2, 0): -dcount(wb3, NG)}
            items = [(g, AR.xarc(g)) for g in gx]
            if any(it[1].end != ('P', 6) for it in items):
                stat['bad-arc'] += 1
                continue
            R = {p: outer([items[p[0]], items[p[1]]]) for p in hy}
            RX = outer(items)
            if RX is None or any(r is None for r in R.values()):
                stat['undetermined'] += 1
                continue
            stat['determined'] += 1
            if not all({0, 1, 2} <= r for r in R.values()) or not {0, 1, 2} <= RX:
                stat['H-FAIL'] += 1
                print('H-FAIL', wa1, wb1, wa2, wb3, R, RX, flush=True)
            out = [p for p in hy if PC not in R[p]]
            ms = {m[p] for p in out}
            if len(ms) > 1:
                stat['P1-FAIL'] += 1
                print('P1-FAIL', wa1, wb1, wa2, wb3, R, m, flush=True)
            stat['pc-in-R' if PC in RX else 'pc-ejected'] += 1
            if PC in RX and out:
                stat['HELLY-PC-FAIL'] += 1
            xs = [cvx(g) for g in gx]
            iscen = lambda b: all(adj(spider(b), x) for x in xs)
            tw = [j for j in range(-M, M + 1) if iscen(D * j if j >= 0 else inv(D) * (-j))]
            yc = [p for p in hy if iscen(hy[p])]
            if PC not in RX:
                mm = ms.pop() if ms else None
                if any(j != mm for j in tw) or any(m[p] != mm for p in yc):
                    stat['P2-FAIL'] += 1
                    print('P2-FAIL', wa1, wb1, wa2, wb3, 'm', m, 'out', out, 'tw', tw, 'yc', yc, flush=True)
            found = bool(tw or yc)
            if not found:
                Dk = {k: (D * k if k >= 0 else inv(D) * (-k)) for k in (-1, 0, 1)}
                for p in hy:
                    for g in [[]] + GV + [inv(x) for x in GV]:
                        for k in Dk:
                            if iscen(hy[p] + g + Dk[k]):
                                found = True
                                break
                        if found:
                            break
                    if found:
                        break
            stat['P3-found' if found else 'P3-notfound'] += 1
            if stat['tuples'] % 20 == 0:
                print('progress', dict(stat), flush=True)
    for k, v in sorted(stat.items()):
        print(' ', k, v)


if __name__ == '__main__':
    main(*[int(x) for x in sys.argv[1:]])
