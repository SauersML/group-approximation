"""Exact double-coset b-length |h|_{K,b} for K = <a, b a b^-2> <= F(a, b).

|h|_{K,b} = least r with h in K b^{+-1} K ... b^{+-1} K (r letters), which is
the distance from K to K h in the coset graph X (edge g joins Kg and Kbg).

Method (conventions of fpbs-fold-bootstrap-seeding-2026-09-17.md §1): pass to
left cosets zK, z = g^{-1}, inside the Cayley tree T'.  hull(zK) = z hull(K),
and hull(K) = {reduced words readable from 0 in the core Gamma_K}.  Two
distinct cosets are adjacent in X iff their hulls meet (neighbours of K are
exactly the cosets zK with z in K{b^{+-1}, b^{+-2}}K = K b^{+-1} K, since
b^2 = c^{-1} b a).  For convex subtrees, a shortest chain K = C_0, ..., C_r =
zK of pairwise-meeting hulls can be taken to consist of hulls meeting the
tree geodesic [1, z]; every vertex y of T' lies only in the hulls of
c_0(y) = yK, c_1(y) = y b^-1 K, c_2(y) = y b^-2 K.  So a BFS over those
finitely many cosets is exact.
"""
from collections import deque

INV = {'a': 'A', 'A': 'a', 'b': 'B', 'B': 'b'}
# core Gamma_K: a-loop at 0; b: 0->1; a: 1->2; b: 1->2
STEP = {(0, 'a'): 0, (0, 'b'): 1, (1, 'a'): 2, (1, 'b'): 2,
        (0, 'A'): 0, (1, 'B'): 0, (2, 'A'): 1, (2, 'B'): 1}


def red(w):
    out = []
    for x in w:
        if out and out[-1] == INV[x]:
            out.pop()
        else:
            out.append(x)
    return ''.join(out)


def inv(w):
    return ''.join(INV[x] for x in reversed(w))


def readable(w, v=0):
    for x in w:
        if (v, x) not in STEP:
            return False
        v = STEP[(v, x)]
    return True


def canon(y):
    """Canonical form of the left coset yK (y reduced), via the right coset
    K y^-1 read into the Schreier graph = core plus hanging trees."""
    g = red(inv(y))
    v = 0
    for i, x in enumerate(g):
        if (v, x) not in STEP:
            return (v, g[i:])
        v = STEP[(v, x)]
    return (v, '')


def meets(z):
    """hull(K) and z hull(K) share a vertex (z reduced)."""
    for i in range(len(z) + 1):
        if readable(z[:i]) and readable(inv(z[i:])):
            return True
    return False


def adjacent(u, v):
    """Hulls of uK and vK meet (u, v reduced representatives)."""
    return meets(red(inv(u) + v))


def b_length(h):
    """Distance in X from K to K h, i.e. from K to h^{-1} K in left form."""
    z = red(inv(h))
    reps = {}
    for i in range(len(z) + 1):
        y = z[:i]
        for suffix in ('', 'B', 'BB'):
            r = red(y + suffix)
            reps.setdefault(canon(r), r)
    start, goal = canon(''), canon(z)
    reps.setdefault(start, '')
    reps.setdefault(goal, z)
    keys = list(reps)
    dist = {start: 0}
    dq = deque([start])
    while dq:
        c = dq.popleft()
        if c == goal:
            return dist[c]
        for d in keys:
            if d not in dist and adjacent(reps[c], reps[d]):
                dist[d] = dist[c] + 1
                dq.append(d)
    raise RuntimeError('chain not found for %s' % h)


if __name__ == '__main__':
    import itertools
    # sanity: K elements have length 0, b^{+-1}, b^{+-2} have length 1
    for h in ('', 'a', 'baBB', 'bbAB', 'b', 'B', 'bb', 'BB'):
        print('|%s|_{K,b} = %d' % (h or '1', b_length(h)))
    for h in ('bab', 'bAb', 'baab', 'bAAb', 'babab', 'bbb', 'bbab', 'bBa',
              'babAb', 'bAbab'):
        print('|%s|_{K,b} = %d' % (h, b_length(red(h))))
    # distribution over all reduced words of length <= 8
    hist = {}
    words = ['']
    for n in range(8):
        words = [w + x for w in words for x in 'aAbB'
                 if not w or w[-1] != INV[x]]
        hist[n + 1] = {}
        for w in words:
            r = b_length(w)
            hist[n + 1][r] = hist[n + 1].get(r, 0) + 1
    for n, hst in hist.items():
        print('word length', n, 'b-length histogram', dict(sorted(hst.items())))
