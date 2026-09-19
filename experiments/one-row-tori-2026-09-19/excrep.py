# excision representations: c on Z/n equals (up to conjugation by a rotation) the first-return map of
# the rotation x->x+r on Z/(n+m) to the complement of the arc [0,m).  Padding back the m points gives
# the commuting pair (+1,+r) on Z/(n+m) at rank distance <= 2m+2 (see note).  mtab(n,mmax) -> dict
# canonical-key -> least m.
import numpy as np
def induced(N, r, m):
    n = N - m; out = np.empty(n, dtype=np.int64)
    for i in range(n):
        y = (i + m + r) % N
        while y < m: y = (y + r) % N
        out[i] = y - m
    return out
def key(c):
    n = len(c); x = np.arange(n); best = None
    for p in range(n):
        cp = tuple(((c[(x + p) % n] - p) % n).tolist())
        if best is None or cp < best: best = cp
    return best
def mtab(n, mmax):
    tab = {}
    for m in range(1, mmax + 1):
        N = n + m
        for r in range(1, N):
            if np.gcd(r, N) != 1 and False: pass
            k = key(induced(N, r, m))
            if k not in tab: tab[k] = m
    return tab
