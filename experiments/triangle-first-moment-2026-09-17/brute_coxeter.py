"""Exact |Hom(W, S_n)| for the Coxeter triangle group W = <a,b,c | a^2,b^2,c^2,(ab)^p,(bc)^q,(ca)^r>
by enumerating triples of elements of order dividing 2 in S_n."""
import sys, itertools
import numpy as np
p, q, r = map(int, sys.argv[1].split(","))
N = int(sys.argv[2])
def compose(x, y):  # (x*y)(i) = x(y(i))
    return tuple(x[i] for i in y)
def order_divides(x, m):
    n = len(x); e = tuple(range(n)); z = e
    for _ in range(m):
        z = compose(x, z)
    return z == e
for n in range(1, N + 1):
    invs = [x for x in itertools.permutations(range(n)) if compose(x, x) == tuple(range(n))]
    L = len(invs)
    def rel(m):
        M = np.zeros((L, L), dtype=np.int64)
        for i, x in enumerate(invs):
            for j, y in enumerate(invs):
                if order_divides(compose(x, y), m):
                    M[i, j] = 1
        return M
    Mp, Mq, Mr = rel(p), rel(q), rel(r)
    # count a,b,c: Mp[a,b] Mq[b,c] Mr[c,a]
    total = int(np.trace(Mp @ Mq @ Mr))
    print(n, total, flush=True)
