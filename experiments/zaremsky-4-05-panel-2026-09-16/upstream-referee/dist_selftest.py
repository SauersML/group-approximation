import random, crit_check as C
from collections import deque
n, adj, k = C.setup('P4')
commute, inv, append, nf, dist = C.make_ops(n, adj)
B = C.ball(n, append, nf, 7)
rng = random.Random(3)
els = [g for g in B if B[g] <= 3]
bad = 0
for _ in range(60):
    g = rng.choice(els)
    # BFS from g inside B (radius 7 covers geodesics between points of B_3 of length <= 6)
    D = {g: 0}; q = deque([g])
    while q:
        u = q.popleft()
        if D[u] >= 6: continue
        for x in range(2*n):
            v = nf(append(list(u), x))
            if v in B and v not in D:
                D[v] = D[u]+1; q.append(v)
    for h in rng.sample(els, 30):
        if D.get(h, 99) != dist(g, h):
            bad += 1
print('paths checked, mismatches:', bad)
