# Sanity checks of mono.py and the first lift tests.
import sys; sys.path.insert(0, sys.path[0])
from mono import *
name = sys.argv[1] if len(sys.argv) > 1 else 'H4'
A = Arr(name); N = A.N; m = N - 1
print(name, 'strands', N, 'nonX', len(A.nonX), 'X', len(A.X))

def br(w):
    b, winv, order = A.braid(w)
    assert order == A.order0, 'not pure'
    return b
def eqP(w1, w2): return same(N, br(w1), br(w2))
def eqB(w1, w2):   # equality after forgetting m (i.e. in B-circ image mu)
    return same(N - 1, forget(br(w1), A.order0, m), forget(br(w2), A.order0, m))
def trivB(w): return eqB(w, [])

print('pure gens have braids of length', [len(br([i, i])) for i in (1, 2, 3, 4)])
print('sigma_1^2 forgets to trivial:', trivB([1, 1]))
rel = {'22_33': ([2, 3, 2, 2, 3, 2], [3, 2, 3, 3, 2, 3]), '12': ([1, 2, 1, 1, 2, 1], [2, 1, 2, 2, 1, 2])}
m34 = dict(MS[name]).get((2, 3), 2)
rel['34'] = ([3, 4] * m34, [4, 3] * m34)
rel['14'] = ([1, 4, 1, 4], [4, 1, 4, 1]); rel['24'] = ([2, 4, 2, 4], [4, 2, 4, 2]); rel['13'] = ([1, 3, 1, 3], [3, 1, 3, 1])
for k, (u, v) in rel.items():
    print('relation', k, 'in P-circ (46-braid):', eqP(u, v), '  after forgetting m:', eqB(u, v))
