"""Reproduce the 13 greedy stalls of w12-124 (certify.py part D, seed 5) and save the stuck pairs."""
from swap import *
import random, json
def components(b, c):
    uf = UF(len(b))
    for x in range(len(b)): uf.u(x, b[x]); uf.u(x, c[x])
    comps = {}
    for x in range(len(b)): comps.setdefault(uf.f(x), []).append(x)
    return list(comps.values())
def restrict(b, c, cm):
    idx = {x: i for i, x in enumerate(cm)}
    return [idx[b[x]] for x in cm], [idx[c[x]] for x in cm]
rng = random.Random(5); out = []
for trial in range(200):
    sizes = [(rng.randrange(4, 10), rng.randrange(4, 10)) for _ in range(rng.randrange(1, 3))]
    b0, c0 = tori(sizes); d = len(b0); m = rng.randrange(2, 6)
    seed = rng.randrange(d); pts = {seed}; r = rng.randrange(1, 4); frontier = [seed]
    for _ in range(r):
        frontier = [g[y] for y in frontier for g in (b0, c0, inv(b0), inv(c0))]; pts |= set(frontier)
    if rng.random() < 0.3: pts |= {rng.randrange(d) for _ in range(3)}
    pts = sorted(pts); b, c = b0[:], c0[:]
    for g, g0 in ((b, b0), (c, c0)):
        sup = rng.sample(pts, min(m, len(pts))); perm = sup[:]; rng.shuffle(perm)
        for u, v in zip(sup, perm): g[u] = g0[v]
    if excess(b, c) == 0: continue
    bb, cc = b[:], c[:]
    while excess(bb, cc) > 0:
        r_ = best_swap(Surf(bb, cc), 7)
        if r_ is None: break
        bb, cc = r_[3], r_[4]
    if excess(bb, cc) > 0:
        out.append(dict(trial=trial, sizes=sizes, b0=b0, c0=c0, b=b, c=c, bs=bb, cs=cc))
        print(trial, sizes, [ (len(cm), excess(*restrict(bb, cc, cm))) for cm in components(bb, cc)], flush=True)
json.dump(out, open('stalls.json', 'w'))
