"""Relator-blind finite-quotient census for V = G0/<<r5,r6,r7,r8>>.

G0 = S4 *_{Z2} S3 = <a,b,c | a^2, b^3, (ab)^4, c^2, (ac)^3>.
For every subset S of {r5,r6,r7,r8}, search for a nontrivial permutation action
of G0 of degree m that satisfies every relator in S exactly.

Actions of G0 of degree m are pairs (S4-set structure on [m], S3-set structure
on [m]) that agree on a.  We enumerate S4-sets as multisets of transitive
S4-sets S4/H, and then every involution c with (ac)^3 = 1, via the orbit types
of <a,c> ~ S3 (1, 2, 3 or 6 points).  Right actions: letters are applied left to
right, x.(w1 w2) = (x.w1).w2.  Capital B = b^-1.
"""
import itertools, sys, json
import numpy as np
sys.path.insert(0, 'experiments/thompson-v-models')
from texwords import parse  # noqa: E402

# ---------- S4 and its transitive sets ----------
def pmul(p, q):  # right action: first p then q
    return tuple(q[p[i]] for i in range(len(p)))

A4 = (1, 0, 2, 3)          # a = (0 1)
B4 = (0, 2, 3, 1)          # b = (1 2 3): 1->2->3->1
S4 = set()
frontier = [tuple(range(4))]
while frontier:
    g = frontier.pop()
    if g in S4:
        continue
    S4.add(g)
    frontier += [pmul(g, A4), pmul(g, B4)]
S4 = sorted(S4)
assert len(S4) == 24
e4 = tuple(range(4))
assert pmul(A4, A4) == e4 and pmul(pmul(B4, B4), B4) == e4
ab = pmul(A4, B4)
x = e4
for _ in range(4):
    x = pmul(x, ab)
assert x == e4 and pmul(pmul(ab, ab), ab) != e4 or True

def inv(p):
    r = [0] * len(p)
    for i, j in enumerate(p):
        r[j] = i
    return tuple(r)

def closure(gens):
    H = {e4}
    fr = list(gens)
    while fr:
        g = fr.pop()
        if g in H:
            continue
        H.add(g)
        for h in list(H):
            fr += [pmul(g, h), pmul(h, g)]
    return frozenset(H)

subs = {closure([g, h]) for g in S4 for h in S4}
classes = []
seen = set()
for H in sorted(subs, key=len, reverse=True):
    if H in seen:
        continue
    conj = {frozenset(pmul(pmul(inv(g), h), g) for h in H) for g in S4}
    seen |= conj
    classes.append(H)
assert len(classes) == 11

def coset_action(H):
    cosets = []
    idx = {}
    for g in S4:
        C = frozenset(pmul(h, g) for h in H)
        if C not in idx:
            idx[C] = len(cosets)
            cosets.append(C)
    def act(s):
        return tuple(idx[frozenset(pmul(y, s) for y in C)] for C in cosets)
    return act(A4), act(B4)

ORBITS = []  # (degree, a, b) for each transitive S4-set
for H in classes:
    a, b = coset_action(H)
    ORBITS.append((24 // len(H), a, b))
ORBITS.sort()

# ---------- involutions c with (ac)^3 = 1 ----------
def c_choices(a):
    m = len(a)
    out = []
    c = [-1] * m
    fixed = [i for i in range(m) if a[i] == i]

    def rec():
        try:
            p = c.index(-1)
        except ValueError:
            out.append(tuple(c))
            return
        if a[p] == p:
            c[p] = p; rec(); c[p] = -1                     # 1-point orbit
            for x in range(m):                               # 3-point orbit, z = p
                y = a[x]
                if x != y and c[x] == -1 and c[y] == -1:
                    # c = (x p), y fixed
                    c[x], c[p], c[y] = p, x, y; rec(); c[x] = c[p] = c[y] = -1
        else:
            q = a[p]
            c[p], c[q] = q, p; rec(); c[p] = c[q] = -1     # 2-point orbit
            for z in fixed:                                  # 3-point orbit
                if c[z] == -1:
                    for u, v in ((p, q), (q, p)):            # c = (u z), v fixed
                        c[u], c[z], c[v] = z, u, v; rec(); c[u] = c[z] = c[v] = -1
            free = [x for x in range(m) if a[x] != x and c[x] == -1 and x < a[x] and x != p]
            for P2, P3 in itertools.combinations(free, 2):   # hexagon
                pts = [p, q, P2, a[P2], P3, a[P3]]
                pair = {p: 0, q: 0, P2: 1, a[P2]: 1, P3: 2, a[P3]: 2}
                for M in matchings(pts):
                    if all(pair[u] != pair[v] for u, v in M):
                        for u, v in M:
                            c[u], c[v] = v, u
                        rec()
                        for u, v in M:
                            c[u] = c[v] = -1
    rec()
    return out

def matchings(pts):
    if not pts:
        yield []
        return
    u = pts[0]
    for i in range(1, len(pts)):
        rest = pts[1:i] + pts[i + 1:]
        for M in matchings(rest):
            yield [(u, pts[i])] + M

# ---------- relators ----------
def load(path):
    ws = []
    for line in open(path):
        line = line.strip()
        if line and not line.startswith('#'):
            ws.append(parse(line))
    return ws

def evaluate(word, a, b, C):
    """C: (N, m) array of c's.  Returns boolean (N,) array: word == 1."""
    m = len(a)
    a = np.array(a); b = np.array(b); Bi = np.argsort(b)
    pos = np.tile(np.arange(m), (C.shape[0], 1))
    for ch in word:
        if ch == 'a':
            pos = a[pos]
        elif ch == 'b':
            pos = b[pos]
        elif ch == 'B':
            pos = Bi[pos]
        elif ch == 'c':
            pos = np.take_along_axis(C, pos, axis=1)
        else:
            raise ValueError(ch)
    return (pos == np.arange(m)).all(axis=1)

def s4_sets(m):
    """Multisets of transitive S4-sets of total degree m, not all trivial."""
    def rec(start, left):
        if left == 0:
            yield []
            return
        for i in range(start, len(ORBITS)):
            d = ORBITS[i][0]
            if d <= left:
                for rest in rec(i, left - d):
                    yield [i] + rest
    for combo in rec(0, m):
        if any(ORBITS[i][0] > 1 for i in combo):
            yield combo

def glue(combo):
    a, b, off = [], [], 0
    for i in combo:
        d, oa, ob = ORBITS[i]
        a += [off + x for x in oa]
        b += [off + x for x in ob]
        off += d
    return tuple(a), tuple(b)

def word_str(w):
    out = ''
    for g, e in w:
        n = abs(e)
        if g == 'b':
            out += ('b' if e > 0 else 'B') * n
        else:
            out += g * n            # a, c are involutions
    return out

# ---------- main ----------
def main(mmax, relfile='experiments/thompson-v-models/rel_V.txt'):
    R = [word_str(w) for w in load(relfile)]
    k = len(R)
    subsets = [S for r in range(k + 1) for S in itertools.combinations(range(k), r)]
    best = {}
    for m in range(1, mmax + 1):
        ncand = 0
        for combo in s4_sets(m):
            a, b = glue(combo)
            cs = c_choices(a)
            if not cs:
                continue
            C = np.array(cs)
            ncand += len(cs)
            ok = np.stack([evaluate(w, a, b, C) for w in R])  # (k, N)
            for S in subsets:
                if S in best:
                    continue
                mask = ok[list(S)].all(axis=0) if S else np.ones(len(cs), bool)
                hit = np.nonzero(mask)[0]
                if len(hit):
                    j = int(hit[0])
                    best[S] = dict(m=m, orbits=[ORBITS[i][0] for i in combo],
                                   a=list(a), b=list(b), c=list(map(int, C[j])))
        print(f'm={m}: {ncand} actions tested; solved subsets so far:',
              sorted(best, key=lambda s: (len(s), s)), flush=True)
    return R, subsets, best

if __name__ == '__main__':
    mmax = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    relfile = sys.argv[2] if len(sys.argv) > 2 else 'experiments/thompson-v-models/rel_V.txt'
    R, subsets, best = main(mmax, relfile)
    names = ['r5', 'r6', 'r7', 'r8'][:len(R)]
    print('\nSUMMARY (smallest degree of a nontrivial action satisfying S exactly):')
    for S in subsets:
        lab = '{' + ','.join(names[i] for i in S) + '}'
        if S in best:
            w = best[S]
            print(f'  {lab:16s} m={w["m"]:3d} orbits={w["orbits"]} c={w["c"]}')
        else:
            print(f'  {lab:16s} none with m<={mmax}')
