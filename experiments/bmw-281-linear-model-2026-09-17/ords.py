import sys, random, numpy as np, itertools
from aut import AUT
from math import gcd
def levelperms(name, n):
    out, sec = AUT[name]; S = sorted(out)
    # perm on leaves at level n, index = sum x_i 3^(n-1-i); build recursively
    P = {a: np.array([out[a][x] for x in range(3)]) for a in S}
    for k in range(2, n+1):
        Q = {}
        for a in S:
            arr = np.empty(3**k, dtype=np.int64)
            m = 3**(k-1)
            for x in range(3):
                arr[x*m:(x+1)*m] = out[a][x]*m + P[sec[a][x]]
            Q[a] = arr
        P = Q
    return P
def compose(p, q): # first q then p: (p∘q)(i) = p[q[i]]
    return p[q]
def order(p):
    n = len(p); seen = np.zeros(n, bool); o = 1
    for i in range(n):
        if not seen[i]:
            j = i; c = 0
            while not seen[j]:
                seen[j] = True; j = p[j]; c += 1
            o = o*c//gcd(o,c)
    return o
if __name__ == '__main__':
    name, n, L, T = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    P = levelperms(name, n); S = sorted(P)
    random.seed(1)
    for t in range(T):
        w = [random.choice(S) for _ in range(L)]
        p = np.arange(3**n)
        for a in w: p = compose(P[a], p)
        print(''.join(map(str,w)), [order(p[: ]) if False else None][0] if False else order(p), end=' | ')
        # orders at lower levels
        res = []
        for k in range(1, n+1):
            q = p[::3**(n-k)] // 3**(n-k)
            res.append(order(q))
        print(res)
