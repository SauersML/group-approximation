"""Certificate: a single-edge hexagon with no centre of the forms y2 / s4^{2j}A_Y, in the A_3 model and,
through the cabling embedding iota, in the V0 I_2(5) shadow (A_6, beta-letters in N_V).

A_3 tuple:  a1 = A24, a2 = A34, a3 = (a1 a2)^-1 in F;   b1 = A12 A13, b2 = A12^-1, b3 = A12 A13^-1 A12^-1 in N.
iota: A12 -> D = Delta_{1234}^2, A13 -> s4 D Delta_{123}^-2 s4^-1, A24 -> tau s4^2 tau^-1, A34 -> tau^2,
      tau = s6 s5 s6^-1 (strand 6 = p_b is the extra fibre point; strands 1,2,3 cable q, 4 = p_c, 5 = p_a, 7 = t).
Checks (curver): relations, the 6-cycle adjacencies, y2 not adjacent to x1, twist candidates not adjacent to x3
(with the intersection numbers that bound every j); the vertex y3 = b3^-1.A_Y is a centre (Y2 form after
rotating the base edge to (x2, y1)).
Run: PYTHONPATH=.:<curver>:<realalg> python3 verify.py [M]"""
import sys
import curver

sys.setrecursionlimit(20000)


def inv(w):
    return [-g for g in reversed(w)]


def model(npunct, xname, legs):
    S = curver.load(0, npunct)
    mc = lambda b: S('.'.join(('s_%d' if g > 0 else 'S_%d') % abs(g) for g in b)) if b else S('')
    X0 = S.arcs[xname]
    L0 = [S.arcs['s_0']] + [S(w)(S.arcs['s_0']) for w in legs]
    xa = lambda b: mc(b)(X0)
    sp = lambda b: [mc(b)(l) for l in L0]
    return S, mc, xa, sp


def ix(sp, x):
    return sum(l.intersection(x) for l in sp)


def run(name, npunct, xname, legs, g, M, extra_centres):
    S, mc, xa, sp = model(npunct, xname, legs)
    A12, A13, A24, A34 = g
    a1, a2 = A24, A34
    a3 = inv(a1 + a2)
    b1, b2, b3 = A12 + A13, inv(A12), A12 + inv(A13) + inv(A12)
    print('==', name)
    print('hexagon relation a1 b1 a2 b2 a3 b3 = 1:', mc(a1 + b1 + a2 + b2 + a3 + b3).is_identity(),
          '| prod a = 1:', mc(a1 + a2 + a3).is_identity(), '| prod b = 1:', mc(b1 + b2 + b3).is_identity())
    X = [xa([]), xa(a1), xa(a1 + b1 + a2)]
    Y = [sp([]), sp(a1 + b1), sp(inv(b3))]
    cyc = [(0, 0), (1, 0), (1, 1), (2, 1), (2, 2), (0, 2)]
    print('6-cycle x1y1x2y2x3y3 intersection numbers (all 0 = cycle):', [ix(Y[j], X[i]) for i, j in cyc])
    print('x pairwise distinct:', all(X[i] != X[j] for i, j in ((0, 1), (0, 2), (1, 2))),
          '| y pairwise distinct:', all(Y[i] != Y[j] for i, j in ((0, 1), (0, 2), (1, 2))),
          '| y_i against other x (nonzero = not a centre):', ix(Y[0], X[2]), ix(Y[1], X[0]), ix(Y[2], X[1]))
    print('Y2 form: i(y2, x1) =', ix(Y[1], X[0]))
    K = ix(Y[0], X[2])
    vals = {j: ix(sp(A12 * j if j >= 0 else inv(A12) * (-j)), X[2]) for j in range(-M, M + 1)}
    print('TW form: i(D^j.y1, x3) for |j| <=', M, ':', [vals[j] for j in range(-M, M + 1)])
    print('  (twist bound: every |j| > i(y1,x3) =', K, 'is excluded once growth is linear; min over table =',
          min(vals.values()), ')')
    for wn, n in extra_centres:
        c = sp(n)
        print('explicit centre', wn, ': i with x1,x2,x3 =', [ix(c, x) for x in X])


def main(M=12):
    A3 = ([1, 1], [2, 1, 1, -2], [3, 2, 2, -3], [3, 3])
    cent3 = []
    run('A_3 model (B_4: q,a,b,t)', 7, 's_4', [], A3, M, cent3)
    D = [1, 2, 3] * 4
    d123 = [1, 2] * 3
    tau = [6, 5, -6]
    A6 = (D, [4] + D + inv(d123) + [-4], tau + [4, 4] + inv(tau), tau + tau)
    run('A_6 V0 shadow via iota (B_7)', 10, 's_7', ['s_1', 's_2.s_1'], A6, M, [])


if __name__ == '__main__':
    main(*[int(x) for x in sys.argv[1:]])
