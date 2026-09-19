import sys; sys.path.insert(0, sys.path[0])
from mono import *
for nm, kw in (('generic', {}), ('L124', dict(xc=[1e-2, 1.3e-2, 2.3, 1.7e-2], eps=1e-2 / 7))):
    A = Arr('H4', **kw)
    for w in ([4], [1], [2], [3], [4, 4], [1, 2, 2, -1, 1, 1], [3, 4]):
        b1, _, o1 = A.braid(w + inv(w))
        print(nm, w, 'w w^-1 trivial:', o1 == A.order0 and same(A.N, b1, []))
