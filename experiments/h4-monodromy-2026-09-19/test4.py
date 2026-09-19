# Braid relation Delta_ij = Delta_ji itself (non-pure half-twist words), base point near L_ij (local)
# and at the generic base point (global standard lifts).
import sys; sys.path.insert(0, sys.path[0])
from mono import *
name = sys.argv[1] if len(sys.argv) > 1 else 'H4'
m = MS[name]
def mij(i, j): return m.get((i, j), m.get((j, i), 2))
for dl in (None, 1e-2, 1e-3):
    for i in range(4):
        for j in range(i + 1, 4):
            if dl is None: A = Arr(name)
            else:
                xc = [3.0, 1.7, 2.3, 5.0]; xc[i] = dl; xc[j] = 1.3 * dl; A = Arr(name, xc=xc, eps=dl / 7)
            k = mij(i, j); p = ([i + 1, j + 1] * k)[:k]; q = ([j + 1, i + 1] * k)[:k]
            try:
                b1, w1, o1 = A.braid(p); b2, w2, o2 = A.braid(q)
                ok = o1 == o2 and np.allclose(w1, w2) and same(A.N, b1, b2)
            except AssertionError as e: ok = 'degenerate'
            print(name, 'base', 'generic' if dl is None else 'near L_%d%d d=%g' % (i + 1, j + 1, dl), 'm=%d' % k, 'Delta=Delta\':', ok)
