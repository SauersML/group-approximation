# Perfectness sanity check of N = <<t>>: every hom Gamma'' -> solvable group must kill t.
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gamma2 import R0, R1
def close(gens, n):
    e = tuple(range(n)); S = {e}; fr = [e]
    while fr:
        new = []
        for a in fr:
            for g in gens:
                b = tuple(a[g[k]] for k in range(n))
                if b not in S: S.add(b); new.append(b)
        fr = new
    return sorted(S)
def test(name, gens, n):
    P = close(gens, n); idx = {p: i for i, p in enumerate(P)}
    mul = [[idx[tuple(a[b[k]] for k in range(n))] for b in P] for a in P]
    inv = [idx[tuple(sorted(range(n), key=lambda k: a[k]))] for a in P]
    e = idx[tuple(range(n))]
    def ev(w, im):
        g = e
        for c in w: g = mul[g][im[c]]
        return g
    bad = tot = 0
    N = len(P)
    for xi in range(N):
        for yi in range(N):
            for ti in range(N):
                im = {'x': xi, 'X': inv[xi], 'y': yi, 'Y': inv[yi], 't': ti, 'T': inv[ti]}
                if ev(R0, im) == e and ev(R1, im) == e:
                    tot += 1; bad += ti != e
    print(name, 'order', N, 'homs', tot, 'with t != 1:', bad, flush=True)
test('S4', [(1,0,2,3), (1,2,3,0)], 4)
test('D5', [(1,2,3,4,0), (0,4,3,2,1)], 5)
test('D6', [(1,2,3,4,5,0), (0,5,4,3,2,1)], 6)
test('Z3wrZ2 (deg 6)', [(1,2,0,3,4,5), (3,4,5,0,1,2)], 6)
test('AGL(1,5)', [(1,2,3,4,0), (0,2,4,1,3)], 5)
