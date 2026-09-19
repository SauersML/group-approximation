# Finite-cover canonical-cycle test for rose mapping tori in other bases of the fibre F_4.
# A basis (b_1..b_4) = alpha(p,q,r,s) gives a rose K(G,1) whose 2-cells are indexed by the b_j.  The canonical
# cycle z_H is the 1-cycle of the loops LOOPS rewritten in b-letters; a one-lift core needs its pushforward to
# the index-9 cover X_L (S_9 action) to have, for each letter, at most one lift with nonzero coefficient.
# Usage: python3 bases.py <w11 dir> <depth>
import sys, itertools
sys.path.insert(0, sys.argv[1])
from fbc import red, inv
X2 = 'rrSqPRs'
LOOPS = [(-1, 'Q' + X2), (1, inv(X2) + 's' + X2), (-2, 'pQ'), (-2, 'qR')]
XY = {'p': 'YYxyy', 'q': 'Yxy', 'r': 'x', 's': 'yxY'}
def perm(cycles, n=9):
    p = list(range(n + 1))
    for cyc in cycles:
        for i, a in enumerate(cyc): p[a] = cyc[(i + 1) % len(cyc)]
    return p
PX, PY = perm([(3, 4, 6, 5), (7, 8, 9)]), perm([(1, 2, 3), (5, 7, 8)])
def act(word, pt):
    for ch in word:
        P = PX if ch.lower() == 'x' else PY
        pt = P[pt] if ch.islower() else P.index(pt)
    return pt
def fperm(c):  # permutation of an old fibre letter
    u = XY[c.lower()] if c.islower() else ''.join(ch.swapcase() for ch in reversed(XY[c.lower()]))
    return [act(u, i) if i else 0 for i in range(10)]
FP = {c: fperm(c) for c in 'pqrsPQRS'}
BASE = [i for i in range(1, 10) if all(act(h, i) == i for h in ['XyxYx', 'Xyyyx', 'XYxyx', 'y', 'xyX'])][0]
def sub(m, u): return red(''.join(m[c] if c.islower() else inv(m[c.lower()]) for c in u))
def moves():
    L = 'pqrs'
    for a, b in itertools.permutations(L, 2):
        for bb in (b, b.upper()):
            yield ('R', a, bb); yield ('L', a, bb)
def mv(m, mvv):  # right/left multiply generator a by bb in the map m (images of the NEW letters)
    k, a, bb = mvv; n = dict(m)
    n[a] = red(m[a] + (m[bb] if bb.islower() else inv(m[bb.lower()]))) if k == 'R' else \
        red((m[bb] if bb.islower() else inv(m[bb.lower()])) + m[a])
    return n
def test(alpha, beta):  # alpha: new letter -> old word;  beta = alpha^-1: old letter -> new word
    push = {}
    for c, l in LOOPS:
        pt = BASE
        for ch in sub(beta, l):
            img = alpha[ch.lower()]
            if ch.islower():
                push[(ch, pt)] = push.get((ch, pt), 0) + c
                for o in img: pt = FP[o][pt]
            else:
                for o in inv(img): pt = FP[o][pt]
                push[(ch.lower(), pt)] = push.get((ch.lower(), pt), 0) - c
    push = {k: v for k, v in push.items() if v}
    ok = all(len([k for k in push if k[0] == e]) <= 1 for e in 'pqrs') and all(abs(v) == 1 for v in push.values())
    return ok, push
if __name__ == '__main__':
    depth = int(sys.argv[2])
    I = {c: c for c in 'pqrs'}
    seen = {tuple(sorted(I.items()))}; front = [(I, I)]; good = 0; tot = 0
    for d in range(depth + 1):
        nxt = []
        for al, be in front:
            tot += 1
            ok, push = test(al, be)
            if ok:
                good += 1
                if good <= 10: print('SURVIVOR depth', d, al, push)
            if d < depth:
                for m in moves():
                    k, a, bb = m
                    inv_m = (k, a, bb.swapcase())
                    al2 = mv(al, m)
                    key = tuple(sorted(al2.items()))
                    if key in seen: continue
                    seen.add(key)
                    # beta2 = alpha2^-1: compose the inverse move on the new letters
                    be2 = {c: sub({x: (x if x != a else (red(x + inv_m[2]) if k == 'R' else red(inv_m[2] + x)))
                                   for x in 'pqrs'}, be[c]) for c in 'pqrs'}
                    assert all(sub(al2, be2[c]) == c for c in "pqrs")
                    nxt.append((al2, be2))
        front = nxt
    print('bases tested:', tot, ' survivors of the index-9 test:', good)
