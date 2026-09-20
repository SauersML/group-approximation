"""Checks for the all-depth proof of (T_j) (double-coset transport).

Proof (research/artifacts/fpbs-doublecoset-transport-all-depths-2026-09-19.md):
the phi-image of the minimal subtree A = T_{L_j} is an explicit subtree of
Y = T_{L_1}; pruning its leaves gives T_{L_{j+1}}.  Hence
  (1) C_{j+1} = Exp(C_j): vertices (0,v) for v whose link has an a-letter,
      (1,v) for v with a b-edge, (2,w) for each b-edge v -> w; edges
      a:(0,v)->(0,va); for each b-edge v->w of C_j:
      b:(0,v)->(1,v), a:(1,v)->(2,w), b:(1,w)->(2,w), b:(0,w)->(1,w)
      (edges at a missing (0,*) vertex are dropped);
  (2) (T_j) fails iff C_j has a vertex with link {b,b^-1} AND one with link
      {a,a^-1};
  (3) no C_j (j >= 0) has a vertex with link {a,a^-1}.
This script checks (1) against the Stallings folding of pb.core for every
j <= JMAX (as base-pointed labelled graphs), and reports the link counts
of (2)/(3).  Usage: python3 transport.py JMAX
"""
import os
import sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'fpbs-overfold-breaker-2026-09-17'))
from pb import core  # noqa: E402

# KEYS = [('a',1),('a',-1),('b',1),('b',-1)]; inverse index
INV = [1, 0, 3, 2]


def expand(nb):
    V = len(nb)
    has_a = [nb[v][0] >= 0 or nb[v][1] >= 0 for v in range(V)]
    has_b = [nb[v][2] >= 0 or nb[v][3] >= 0 for v in range(V)]
    idx = {}

    def vid(key):
        if key not in idx:
            idx[key] = len(idx)
        return idx[key]
    vid((0, 0))                         # base first (base has an a-loop)
    edges = []                          # (x, letter, y)
    for v in range(V):
        if has_a[v]:
            vid((0, v))
        if has_b[v]:
            vid((1, v))
    for v in range(V):
        w = nb[v][0]
        if w >= 0:
            edges.append(((0, v), 0, (0, w)))
        w = nb[v][2]
        if w >= 0:
            vid((2, w))
            edges.append(((1, v), 0, (2, w)))
            edges.append(((1, w), 2, (2, w)))
            for x in (v, w):
                if has_a[x]:
                    edges.append(((0, x), 2, (1, x)))
    enb = [[-1] * 4 for _ in range(len(idx))]
    for (x, k, y) in set(edges):
        X, Y = idx[x], idx[y]
        assert enb[X][k] in (-1, Y) and enb[Y][INV[k]] in (-1, X), 'not folded'
        enb[X][k] = Y
        enb[Y][INV[k]] = X
    return enb


def isomorphic(n1, n2):
    """Base-pointed labelled isomorphism of two connected folded graphs."""
    if len(n1) != len(n2):
        return False
    m = {0: 0}
    st = [0]
    while st:
        v = st.pop()
        for k in range(4):
            a, b = n1[v][k], n2[m[v]][k]
            if (a < 0) != (b < 0):
                return False
            if a < 0:
                continue
            if a in m:
                if m[a] != b:
                    return False
            else:
                m[a] = b
                st.append(a)
    return len(m) == len(n1) and len(set(m.values())) == len(n1)


def links(nb):
    bb = sum(1 for r in nb if r[0] < 0 and r[1] < 0 and r[2] >= 0 and r[3] >= 0)
    aa = sum(1 for r in nb if r[0] >= 0 and r[1] >= 0 and r[2] < 0 and r[3] < 0)
    leaves = sum(1 for r in nb if sum(1 for x in r if x >= 0) < 2)
    return bb, aa, leaves


def main():
    jmax = int(sys.argv[1])
    C = [core(j)[0] for j in range(jmax + 1)]
    ok = True
    for j in range(jmax + 1):
        bb, aa, lv = links(C[j])
        line = 'j %d |C_j| %d  link{b,B} %d  link{a,A} %d  leaves %d' % (
            j, len(C[j]), bb, aa, lv)
        if j < jmax:
            E = expand(C[j])
            iso = isomorphic(E, C[j + 1])
            ok &= iso
            line += '  Exp(C_j)=C_{j+1}: %s' % iso
        ok &= (aa == 0 and lv == 0)
        print(line)
    print('ALL OK' if ok else 'FAIL')


if __name__ == '__main__':
    main()
