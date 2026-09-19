"""Full transfer (w14-124).  At a cone point A of excess k, let s_0, ..., s_k be the outgoing states one full turn
apart (every 4th corner in ccw order) and P_j the path with a fixed word w from s_j.  Assume the P_j have pairwise
distinct interior vertices, none equal to A or to any end, and ends B_j != A.  Swap P_0 with P_1, then (in the new
surface, same start states and word) P_1 with P_2, ..., P_(k-1) with P_k.  Prediction: each swap changes the excess by
0, or by -2 exactly when the current ends of P_0 and P_j are the same vertex; at the end A's corners all lie in
regular vertices (the excess of A has left A).
Usage: python3 fulltransfer.py SEED TRIALS L"""
import random, sys
from collections import Counter
from swap import Surf, excess, tori, perturb_local, apply_swap
from transfer import ccw, words

def paths(S, starts, w):
    out = []
    for s in starts:
        P = [s]
        for mv in w: P.append(S.step(P[-1], mv))
        out.append(P)
    return out

def trial(b, c, A, starts, w, tally):
    S = Surf(b, c); Ps = paths(S, starts, w)
    ends = [S.vend(P[-1]) for P in Ps]
    inner = [S.vend(st) for P in Ps for st in P[:-1]]
    if A in ends or len(set(inner)) != len(inner) or set(inner) & (set(ends) | {A}): return
    corners_A = [4 * s[0] + s[1] for s in ccw(S, starts[0])]
    for j in range(1, len(starts)):
        S = Surf(b, c); P0, Pj = paths(S, [starts[j - 1], starts[j]], w)
        same = S.vend(P0[-1]) == S.vend(Pj[-1])
        r = apply_swap(S, P0, Pj)
        if r is None: tally['edge-clash'] += 1; return
        e0, e1 = excess(b, c), excess(*r)
        ok = (e1 - e0) == (-2 if same else 0)
        tally[('step', ok, same)] += 1
        b, c = r
    S = Surf(b, c)
    tally[('A-cleared', all(len(S.cls[S.lab[x]]) == 4 for x in corners_A))] += 1

if __name__ == '__main__':
    seed, trials, L = map(int, sys.argv[1:4])
    rng = random.Random(seed); tally = Counter()
    for t in range(trials):
        n = rng.choice((6, 7, 8, 9)); b0, c0 = tori([(n, n)])
        b, c = perturb_local(b0, c0, rng.randrange(1, 6), rng, 3)
        S = Surf(b, c)
        for A in S.cones():
            o = ccw(S, next((i // 4, i % 4) for i in S.cls[A])); M = len(o)
            for r0 in range(4):
                starts = [o[r0 + 4 * j] for j in range(M // 4)]
                for ell in range(L):
                    for w in words(ell): trial(b, c, A, starts, w, tally)
    print(sorted(tally.items(), key=str))
