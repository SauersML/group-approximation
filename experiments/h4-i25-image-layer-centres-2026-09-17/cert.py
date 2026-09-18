"""Ejected-cluster test on w7-042's cabled certificate hexagon (verify.py, V0 shadow, C = {1,2,3,4}).
Tuple: a1 = i(A24), a2 = i(A34), b1 = i(A12 A13), b3 = i(A12 A13^-1 A12^-1), with i(A12) = D, f(i(A13)) = 1,
so m12 = 0, m23 = 1, m31 = 0.  The certificate has no twist centre D^j.spider0 (|j| <= M) and y31 as a centre.
The theorem predicts: p_c (puncture 3) ejected from R; every ejecting pair has the same m; that m equals the class
of every image-layer centre, hence m = m31 = 0, so pair 23 (m = 1) must NOT eject p_c.
Run: ARCS_N=7 PYTHONPATH=.:<curver>:<realalg> python3 cert.py [M]"""
import os, sys
os.environ.setdefault('ARCS_N', '7')
from a6 import inv, spider, xarc as cvx, adj, D
import arcs as AR
from search import outer

PC = 3


def main(M=6):
    d123 = [1, 2] * 3
    tau = [6, 5, -6]
    A12, A13, A24, A34 = D, [4] + D + inv(d123) + [-4], tau + [4, 4] + inv(tau), tau + tau
    a1, a2 = A24, A34
    b1, b3 = A12 + A13, A12 + inv(A13) + inv(A12)
    gx = [[], a1, a1 + b1 + a2]
    hy = {(0, 1): [], (1, 2): a1 + b1, (2, 0): inv(b3)}
    m = {(0, 1): 0, (1, 2): 1, (2, 0): 0}
    items = [(g, AR.xarc(g)) for g in gx]
    print('x-arc ends', [it[1].end for it in items])
    R = {p: outer([items[p[0]], items[p[1]]]) for p in hy}
    RX = outer(items)
    print('R_ij', {p: sorted(r) if r is not None else None for p, r in R.items()}, 'R', sorted(RX) if RX else RX)
    xs = [cvx(g) for g in gx]
    iscen = lambda b: all(adj(spider(b), x) for x in xs)
    print('pair adjacency check (y_ij ~ x_i, x_j):', all(adj(spider(hy[p]), xs[p[0]]) and adj(spider(hy[p]), xs[p[1]]) for p in hy))
    tw = [j for j in range(-M, M + 1) if iscen(D * j if j >= 0 else inv(D) * (-j))]
    yc = [p for p in hy if iscen(hy[p])]
    print('twist centres j (|j| <=', M, '):', tw, '| vertex centres:', yc, 'with m', [m[p] for p in yc])
    if RX is not None and None not in R.values():
        out = [p for p in hy if PC not in R[p]]
        print('p_c in R:', PC in RX, '| ejecting pairs', out, 'm there', [m[p] for p in out])
        ok = (PC in RX) or (len({m[p] for p in out}) == 1 and all(m[p] == m[out[0]] for p in yc)
                            and all(j == m[out[0]] for j in tw))
        print('prediction (P1)+(P2) holds:', ok)


if __name__ == '__main__':
    main(*[int(x) for x in sys.argv[1:]])
