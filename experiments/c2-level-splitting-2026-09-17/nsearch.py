# Beam search over Whitehead-equivalent one-relator presentations of H = <b,c,d,e | R>, minimising the
# Moldavanskii width W = sum_g (nu_g - mu_g) over a stable letter t with eps(t) = +-1.  Base L is free
# (L <= N <= F_4), so W is the rank of the edge group; an FFLS of this shape needs W <= 3 and A a free factor.
import sys, itertools, heapq
from hlib import *
X = 'bcde'
def hr(u):
    o = []
    for c in u:
        if o and o[-1] == c.swapcase(): o.pop()
        else: o.append(c)
    return ''.join(o)
def cyc(u):
    u = hr(u)
    while len(u) > 1 and u[0] == u[-1].swapcase(): u = u[1:-1]
    return u
def canon(u):
    c = [u[i:] + u[:i] for i in range(len(u))]; ci = [hinv(v) for v in c]
    return min(c + ci)
def app(m, u): return hr(''.join(m[c] if c.islower() else hinv(m[c.lower()]) for c in u))
def wh(a, S_):
    m = {}
    for x in X:
        w = x
        if x in S_: w = w + a
        if x.upper() in S_: w = a.swapcase() + w
        m[x] = w
    return m
AUTS = []
L8 = list(X) + [c.upper() for c in X]
for a in L8:
    oth = [c for c in L8 if c.lower() != a.lower()]
    for k in range(1, len(oth) + 1):
        for S_ in itertools.combinations(oth, k): AUTS.append((wh(a, set(S_)), wh(a.swapcase(), set(S_))))
def epsw(img, g): return eps(img[g])       # img[g] = word in original b,c,d,e
def width(rel, img):
    E_ = {g: epsw(img, g) for g in X}
    best = None
    for t in X:
        if abs(E_[t]) != 1: continue
        # rewrite: in rel, letter t has height sign E_[t]; others g0 = g t^-E_[g] (in t-heights)
        lift = {g: E_[g] * E_[t] for g in X}     # heights measured in units of t^{E_t}
        out, j = [], 0
        for c in rel:
            g = c.lower()
            if g == t: j += (1 if c.islower() else -1); continue
            if c.islower(): out.append((g, j)); j += lift[g]
            else: j -= lift[g]; out.append((g, j))
        if j != 0: return None
        W = 0; rng = {}
        for g, jj in out: rng.setdefault(g, []).append(jj)
        W = sum(max(v) - min(v) for v in rng.values())
        cand = (W, t, {g: (min(v), max(v)) for g, v in rng.items()})
        if best is None or cand[0] < best[0]: best = cand
    return best
def search(maxlen=26, beam=4000, depth=12):
    img0 = {g: g for g in X}
    start = (cyc(R), img0)
    seen = {canon(cyc(R))}; front = [start]; bestW = None; log = []
    for d in range(depth):
        nxt = []
        for rel, img in front:
            for m, mi in AUTS:
                r2 = cyc(app(m, rel))
                if len(r2) > maxlen: continue
                k = canon(r2)
                if k in seen: continue
                seen.add(k)
                img2 = {g: hr(''.join(img[c] if c.islower() else hinv(img[c.lower()]) for c in mi[g])) for g in X}
                w = width(r2, img2)
                if w is None: continue
                nxt.append((w[0], len(r2), r2, img2, w))
        nxt.sort(key=lambda z: (z[0], z[1]))
        front = [(z[2], z[3]) for z in nxt[:beam]]
        if nxt:
            z = nxt[0]; print('depth', d + 1, 'states', len(nxt), 'best W', z[0], 'len', z[1], z[2], z[4][1], z[4][2], flush=True)
            log.append(z)
        if not front: break
    return log
if __name__ == '__main__':
    print('start', width(cyc(R), {g: g for g in X}))
    search(int(sys.argv[1]) if len(sys.argv) > 1 else 26, int(sys.argv[2]) if len(sys.argv) > 2 else 3000, int(sys.argv[3]) if len(sys.argv) > 3 else 8)
