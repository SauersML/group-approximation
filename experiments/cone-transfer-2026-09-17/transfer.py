"""Excess transfer (w14-124).  Two paths P1, P2 with the same move word leave one vertex A in two sectors of
the same direction, have distinct edges, pairwise distinct interior vertices (distinct from A and from the
ends), and end at distinct vertices B1, B2 != A.  Prediction: the swap keeps the total excess; A splits into
two vertices whose corner counts are the two arcs cut by the first edges; B1 and B2 merge.  So choosing
sectors one full turn apart (arc of 4 corners) moves one unit of excess from A to B1 u B2.

Usage: python3 transfer.py SEED TRIALS L"""
import random, sys
from collections import Counter
from swap import Surf, excess, tori, perturb_local, apply_swap, vertices

def rot(S, st):
    x, k = st; N = [S.ci, S.b, S.c, S.bi]
    return (N[(k - 1) % 4][x], (k + 1) % 4)

def ccw(S, st0):
    o = [st0]; st = rot(S, st0)
    while st != st0: o.append(st); st = rot(S, st)
    return o

def check(S, A, s1, s2, word, tally):
    P1, P2 = [s1], [s2]
    for mv in word: P1.append(S.step(P1[-1], mv)); P2.append(S.step(P2[-1], mv))
    B1, B2 = S.vend(P1[-1]), S.vend(P2[-1])
    inner = [S.vend(st) for st in P1[:-1]] + [S.vend(st) for st in P2[:-1]]
    if B1 == B2 or A in (B1, B2): return
    if len(set(inner)) != len(inner) or set(inner) & {A, B1, B2}: return
    r = apply_swap(S, P1, P2)
    if r is None: return
    order = ccw(S, s1); M = len(order); m = order.index(s2)
    old = Counter(len(cl) for cl in S.cls.values())
    pred = old.copy()
    for v in (A, B1, B2): pred[len(S.cls[v])] -= 1
    pred[m] += 1; pred[M - m] += 1; pred[len(S.cls[B1]) + len(S.cls[B2])] += 1
    pred = +pred
    new = Counter(len(cl) for cl in vertices(*r)[1].values())
    ok = (new == pred) and excess(*r) == excess(S.b, S.c)
    tally[(ok, len(word) + 1)] += 1
    if not ok and tally['bad_shown'] < 3:
        tally['bad_shown'] += 1; print('MISMATCH', A, s1, s2, word, dict(old), dict(new), dict(pred))

def words(L):
    if L == 0: yield (); return
    for w in words(L - 1):
        for mv in (0, 1, 2): yield w + (mv,)

def run(b, c, L, tally):
    S = Surf(b, c)
    for A in S.cones():
        o = ccw(S, next((i // 4, i % 4) for i in S.cls[A]))
        for i, s1 in enumerate(o):
            for s2 in o[i + 1:]:
                if s1[1] != s2[1]: continue
                for ell in range(L):
                    for w in words(ell): check(S, A, s1, s2, w, tally)

if __name__ == '__main__':
    seed, trials, L = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    rng = random.Random(seed); tally = Counter()
    for t in range(trials):
        n = rng.choice((6, 7, 8)); b0, c0 = tori([(n, n)])
        b, c = perturb_local(b0, c0, rng.randrange(1, 5), rng, 3)
        if excess(b, c): run(b, c, L, tally)
    print(sorted((k, v) for k, v in tally.items() if k != 'bad_shown'))
