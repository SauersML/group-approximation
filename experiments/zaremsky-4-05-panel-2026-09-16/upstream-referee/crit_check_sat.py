"""Saturated-S variant of crit_check.py: S = maximal diameter-t sets built greedily
from shuffled points of B_t, so Y(S) is small. Usage: GRAPH t trials seed maxS"""
import sys, random, itertools
import crit_check as C
name, t, trials, seed, maxS = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
rng = random.Random(seed)
n, adj, k = C.setup(name)
commute, inv, append, nf, dist = C.make_ops(n, adj)
r = int((k * t) / (k + 1) + k / 2 + 1e-9)
B = C.ball(n, append, nf, t)
Bt = list(B); Br = [g for g in B if B[g] <= r]
far = [g for g in B if B[g] == t]
print(name, 'k', k, 't', t, 'r', r, flush=True)
st = {'trials': 0, 'emptyY': 0, 'nocentre': 0, 'maxS': 0, 'minY': 10**9, 'minslack': 10**9}
for tr in range(trials):
    S = [(), rng.choice(far)]
    pool = rng.sample(Bt, min(len(Bt), 3000))
    for g in pool:
        if len(S) >= maxS: break
        if g not in S and all(dist(g, s) <= t for s in S):
            S.append(g)
    Y = [y for y in Br if all(dist(y, s) <= r for s in S)]
    st['trials'] += 1; st['maxS'] = max(st['maxS'], len(S)); st['minY'] = min(st['minY'], len(Y))
    if not Y:
        st['emptyY'] += 1; print('EMPTY', S, flush=True); continue
    best = min(max(dist(y0, y) for y in Y) for y0 in Y)
    st['minslack'] = min(st['minslack'], t - best)
    if best > t:
        st['nocentre'] += 1; print('NOCENTRE', S, flush=True)
print(st, flush=True)
