"""Certificates for excised-square-kills-cone-local-slit-pair-repair.  Run: python3 certify.py > summary.txt
  A. two-torus cross slit, p = 3..7: shortest excess-lowering slit-pair swap and greedy closing.
  B. excised square on the n x n torus: vertex structure (one 6pi cone point + one flat 1x1 torus),
     profile lower bound, excess after the donor-neutral first undo step, n = 5..40.
  C. excised square, n = 4..7: every slit-pair swap from the cone point with <= 10 edges; the shortest lowering one.
  D. greedy shortest-lowering-swap repair on random clustered perturbations of tori (seed 5): stuck cases and
     their component structure (a small flat torus stranded next to an excess-2 component).
"""
from swap import *
import random

def components(b, c):
    uf = UF(len(b))
    for x in range(len(b)): uf.u(x, b[x]); uf.u(x, c[x])
    comps = {}
    for x in range(len(b)): comps.setdefault(uf.f(x), []).append(x)
    out = []
    for cm in comps.values():
        idx = {x: i for i, x in enumerate(cm)}
        out.append((len(cm), excess([idx[b[x]] for x in cm], [idx[c[x]] for x in cm])))
    return sorted(out)

print("A. two-torus cross slit")
for p in range(3, 8):
    b, c = two_torus_cross(p); r = best_swap(Surf(b, c), 6)
    print("  p=%d excess %d  shortest lowering swap: %d edges, cost (rank b, rank c) = %s, new excess %d;"
          " greedy dist %s" % (p, excess(b, c), r[0], r[1], r[2], greedy(b, c, 6)[0]))

print("B. excised square")
for n in (5, 6, 7, 9, 12, 17, 25, 40):
    b0, c0, b, c = excised(n); S = Surf(b, c)
    db = rank_minus_I(comp(inv(b0), b)); dc = rank_minus_I(comp(inv(c0), c))
    rho = profile(b, c, 12)[0] if n <= 17 else float('nan')
    print("  n=%d dist-to-(b0,c0) (%d,%d) excess %d cone angles/2pi %s components (size,excess) %s"
          " rho(s,t<=12)>=%.3f excess after restoring b only %d"
          % (n, db, dc, excess(b, c), [len(S.cls[v]) // 4 for v in S.cones()], components(b, c), rho,
             excess(b0, c)))

print("C. slit-pair swaps from the cone point of the excised square (all words <= 10 edges)")
for n in (4, 5, 6, 7):
    b0, c0, b, c = excised(n); S = Surf(b, c)
    best = search_all(S, 10, excess(b, c))
    L = min(best)
    print("  n=%d shortest lowering swap %d edges (= n-1), min cost at that length %s; lengths found %s"
          % (n, L, best[L], sorted(best)))

print("D. greedy repair on clustered perturbations (Lmax 7)")
rng = random.Random(5); n_ = 0; stuck = []
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
    n_ += 1; bb, cc = b[:], c[:]
    while excess(bb, cc) > 0:
        r_ = best_swap(Surf(bb, cc), 7)
        if r_ is None: break
        bb, cc = r_[3], r_[4]
    if excess(bb, cc) > 0: stuck.append((sizes, components(b, c), components(bb, cc)))
print("  %d non-commuting instances, %d stuck" % (n_, len(stuck)))
for s in stuck: print("   tori %s start comps %s -> stuck comps %s" % s)
