"""Self-test: ri_k1's exact procedure must detect the known non-malnormal
(RI) counterexample of w19-fp-last1: B = <b, a b^2 a^-1> = psi(F) with
psi(a)=b, psi(b)=a b^2 a^-1, X = psi(ker(F -> S3; a->(123), b->(12))).
It must also report 0 violations for B = L_1 on the same kernel type."""
from folding import *
from ri_k1 import pullback, compact, relrank_le1


def kernel_gens(perms):
    """Schreier generators of the stabiliser of 0 for a permutation action."""
    pa, pb = perms
    n = len(pa)
    word = {0: ''}
    q = [0]
    edges = []
    for v in q:
        for l, p in (('a', pa), ('b', pb)):
            t = p[v]
            edges.append((v, l, t))
            if t not in word:
                word[t] = word[v] + l
                q.append(t)
    inv = lambda w: ''.join(INV[c] for c in reversed(w))
    gens = [reduce_word(word[u] + l + inv(word[v])) for (u, l, v) in edges]
    return [g for g in gens if g]


def subst(w, img):
    out = ''
    for c in w:
        out += img[c] if c in 'ab' else ''.join(INV[d] for d in reversed(img[c.lower()]))
    return reduce_word(out)


def run(img, perms, label):
    X0 = kernel_gens(perms)
    X = [subst(w, img) for w in X0]
    nx, Ex = compact(*graph_of(X))
    nB, EB = graph_of([img['a'], img['b']])
    viol = 0
    for u in range(nx):
        for w in range(u + 1, nx):
            m, F, _ = fold(nx, Ex, [(u, w)])
            ny, Ey = compact(*pullback(m, F, nB, EB))
            if relrank_le1(nx, Ex, ny, Ey) is None:
                viol += 1
    print(label, 'rk X =', rank(nx, Ex), 'violating pairs:', viol)
    return viol


# regular action of S3 on itself: a -> (123), b -> (12), 6 points
import itertools
S3 = list(itertools.permutations(range(3)))
mul = lambda p, q: tuple(q[p[i]] for i in range(3))  # p then q
A, Bp = (1, 2, 0), (1, 0, 2)
pa = [S3.index(mul(s, A)) for s in S3]
pb = [S3.index(mul(s, Bp)) for s in S3]
v1 = run({'a': 'b', 'b': 'abbA'}, (pa, pb), 'non-malnormal psi-host:')
v2 = run({'a': 'a', 'b': 'baBB'}, (pa, pb), 'L_1 host:')
assert v1 > 0, 'selftest failed: known counterexample not detected'
print('selftest OK')
