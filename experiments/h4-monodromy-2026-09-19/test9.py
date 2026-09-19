# The default base point (xc=[3,.1,.2,5], yc=[1,1.3,.7,1.1], eps=.37) and perturbations of it.
import sys, random; sys.path.insert(0, sys.path[0])
from mono import *
P3, P2, P1 = [1, 1], [1, 2, 2, -1], [1, 2, 3, 3, -2, -1]
a = P2 + P3; b = P1 + P3; c = [4, 4]; d = [-3, 4, 4, 3]; w = [2, 3, 4, 4, -3, -2]; u = w + c; v = w + d
rng = random.Random(1); tally = {}
for trial in range(10):
    s = 0 if trial == 0 else 0.1
    xc = list(np.array([3.0, .1, .2, 5.0]) * (1 + s * np.array([rng.uniform(-1, 1) for _ in range(4)])))
    yc = list(np.array([1.0, 1.3, .7, 1.1]) * (1 + s * np.array([rng.uniform(-1, 1) for _ in range(4)])))
    for eps in (0.37, 0.05, 1.0):
        try:
            A = Arr('H4', xc=xc, yc=yc, eps=eps); N = A.N; m = N - 1
            br = lambda x: A.braid(x)[0]; eq = lambda x, y: same(N, br(x), br(y))
            r = (eq(com(u, a), com(v, b)), eq(com(c, a), []), eq(com(w, inv(b) + a), []),
                 same(N - 1, forget(br(a), A.order0, m), []), same(N - 1, forget(br(b), A.order0, m), []))
        except AssertionError: r = 'degenerate'
        print(np.round(xc, 3), np.round(yc, 2), eps, '| coinc, [c,a], [w,b^-1a], a in F45, b in F45:', r)
        tally[r] = tally.get(r, 0) + 1
print(tally)
