# Robustness over base points: random (x, y) in the fundamental chamber, several eps.  For each: does
# the w15 coincidence hold as a 46-braid (in P-circ), do its component identities hold, is the base
# part of a trivial (a~ in F_45), and does the X-relation (2,4) hold?
import sys, random; sys.path.insert(0, sys.path[0])
from mono import *

P3, P2, P1 = [1, 1], [1, 2, 2, -1], [1, 2, 3, 3, -2, -1]
a = P2 + P3; b = P1 + P3; c = [4, 4]; d = [-3, 4, 4, 3]; w = [2, 3, 4, 4, -3, -2]; u = w + c; v = w + d
rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 5); tally = {}
for trial in range(int(sys.argv[2]) if len(sys.argv) > 2 else 12):
    xc = [rng.uniform(0.05, 5) for _ in range(4)]; yc = [rng.uniform(0.05, 5) for _ in range(4)]
    eps = rng.choice([0.05, 0.2, 0.5])
    try:
        A = Arr('H4', xc=xc, yc=yc, eps=eps); N = A.N; m = N - 1
        br = lambda x: A.braid(x)[0]
        eq = lambda x, y: same(N, br(x), br(y))
        r = (eq(com(u, a), com(v, b)), eq(com(c, a), []), eq(com(w, inv(b) + a), []),
             same(N - 1, forget(br(a), A.order0, m), []), eq([2, 4, 2, 4], [4, 2, 4, 2]))
    except AssertionError as e: r = 'degenerate'
    print('x', np.round(xc, 2), 'eps', eps, '| coinc, [c,a]=1, [w,b^-1a]=1, a in F45, rel24:', r)
    tally[r] = tally.get(r, 0) + 1
print(tally)
