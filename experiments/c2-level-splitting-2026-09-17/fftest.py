# For every Whitehead-equivalent presentation (BFS to given depth) with Moldavanskii width <= 3,
# compute the edge group A = <g_j : mu_g <= j < nu_g> in F_4 and test whether it is a free factor.
import sys
from nsearch import *
from ff import is_free_factor, rank as frank
def symword(img, g, t, j):
    """F_4 word of d^j-type conjugate: g0 = g t^-eps(g)eps(t) at t-height j, via the map to G."""
    et = eps(img[t]); eg = eps(img[g])
    gx = toxy(img[g]) + (toxy(hinv(img[t])) if et == 1 else toxy(img[t])) * (eg * et if eg * et > 0 else 0) \
         + (toxy(img[t]) if et == 1 else toxy(hinv(img[t]))) * (-eg * et if eg * et < 0 else 0)
    T = toxy(img[t]) if et == 1 else toxy(hinv(img[t]))
    w = T * j + gx + inv(T) * j if j >= 0 else inv(T) * (-j) + gx + T * (-j)
    return tofib(red(w))
def test(rel, img, w):
    W, t, rng = w
    A = [symword(img, g, t, j) for g, (lo, hi) in rng.items() for j in range(lo, hi)]
    return is_free_factor(A), A
depth = int(sys.argv[1]) if len(sys.argv) > 1 else 2
img0 = {g: g for g in X}
front = [(cyc(R), img0)]; seen = {canon(cyc(R))}; nfound = 0
for d in range(depth):
    nxt = []
    for rel, img in front:
        for m, mi in AUTS:
            r2 = cyc(app(m, rel))
            if len(r2) > 22: continue
            k = canon(r2)
            if k in seen: continue
            seen.add(k)
            img2 = {g: hr(''.join(img[c] if c.islower() else hinv(img[c.lower()]) for c in mi[g])) for g in X}
            w = width(r2, img2)
            if w is None: continue
            nxt.append((r2, img2))
            if w[0] <= 3:
                (ok, k_, s_), A = test(r2, img2, w); nfound += 1
                if nfound <= 12 or ok:
                    print('d', d + 1, r2, w[1], w[2], 'rankA', k_, 'minsize', s_, 'FREE FACTOR' if ok else 'no', flush=True)
                    if ok: print('  gens', {g: img2[g] for g in X}, 'A', A)
    front = nxt
    print('depth', d + 1, 'states', len(nxt), 'W<=3 so far', nfound, flush=True)
