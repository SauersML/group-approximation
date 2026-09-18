"""Single-edge geodesic divergence D(g,s) for F over A_k.

D(g,s) = min over geodesic paths p to g and q to h = g s of max_t d(p(t), q(t)),
where paths are parametrised by time and stay at their endpoint after arrival.
Any geodesic automatic structure with fellow-traveller constant K has K >= D(g,s)
for every edge.  Distances d(u,w) = |u^-1 w| are looked up in the ball B_r;
values > r are reported as r+1.

usage: single_edge.py k R r [top]
"""
import sys, time
from geocomb_sat import Grp, build, word_of


def D_edge(G, dist, I, ballr, r, g, h):
    ng, nh = dist[g], dist[h]
    T = max(ng, nh)
    lay = lambda x, t: I[x][t] if t <= dist[x] else [x]
    dcache = {}

    def d(u, w):
        key = (u, w)
        v = dcache.get(key)
        if v is None:
            v = ballr.get(G.mul(G.inv(u), w), r + 1)
            dcache[key] = v
        return v
    succ_cache = {}

    def succ(x, t, u):
        # successors of u at time t on geodesics to x
        if t >= dist[x]:
            return [x]
        key = (x, t, u)
        s = succ_cache.get(key)
        if s is None:
            nxt = set(I[x][t + 1])
            s = [G.mul(u, a) for a in G.S if G.mul(u, a) in nxt]
            succ_cache[key] = s
        return s
    for K in range(0, r + 2):
        cur = {(G.id, G.id)}
        ok = True
        for t in range(0, T):
            nxt = set()
            for (u, w) in cur:
                for u2 in succ(g, t, u):
                    for w2 in succ(h, t, w):
                        if d(u2, w2) <= K:
                            nxt.add((u2, w2))
            if not nxt:
                ok = False
                break
            cur = nxt
        if ok:
            return K
    return r + 1


def main():
    k = int(sys.argv[1]); R = int(sys.argv[2]); r = int(sys.argv[3])
    top = int(sys.argv[4]) if len(sys.argv) > 4 else 8
    G = Grp("F", k)
    t0 = time.time()
    dist, layers, elems, I, _ = build(G, R, 0)
    ballr = {x: dv for x, dv in dist.items() if dv <= r}
    if r > R:
        raise SystemExit("need r <= R")
    res = []
    for g in elems:
        for s in G.S:
            h = G.mul(g, s)
            if h not in dist or dist[h] < dist[g]:
                continue
            res.append((D_edge(G, dist, I, ballr, r, g, h), dist[g], dist[h], word_of(G, dist, g), word_of(G, dist, s)))
    res.sort(key=lambda x: -x[0])
    hist = {}
    for x in res:
        hist[x[0]] = hist.get(x[0], 0) + 1
    print("k=%d R=%d r=%d edges=%d hist=%s (%.1fs)" % (k, R, r, len(res), sorted(hist.items()), time.time() - t0))
    for x in res[:top]:
        print("  D=%d |g|=%d |h|=%d g=%s s=%s" % x)




def geodesics(G, dist, I, x):
    """all geodesic vertex sequences 1 = p(0), ..., p(|x|) = x"""
    n = dist[x]
    out = [[G.id]]
    for t in range(n):
        nxt = set(I[x][t + 1])
        new = []
        for p in out:
            for a in G.S:
                v = G.mul(p[-1], a)
                if v in nxt:
                    new.append(p + [v])
        out = new
    return out


def D_fixed(G, dist, I, ballr, r, q, g):
    """min over geodesics p to g of max_t d(q(t), p(t)); q is a fixed vertex list"""
    T = max(len(q) - 1, dist[g])
    qa = lambda t: q[t] if t < len(q) else q[-1]
    def d(u, w):
        return ballr.get(G.mul(G.inv(u), w), r + 1)
    for K in range(0, r + 2):
        cur = {G.id}
        for t in range(T):
            nxt = set()
            for u in cur:
                if t >= dist[g]:
                    cands = [g]
                else:
                    lay = set(I[g][t + 1])
                    cands = [G.mul(u, a) for a in G.S if G.mul(u, a) in lay]
                for v in cands:
                    if d(qa(t + 1), v) <= K:
                        nxt.add(v)
            cur = nxt
            if not cur:
                break
        if cur:
            return K
    return r + 1


def vertex_main():
    k = int(sys.argv[2]); R = int(sys.argv[3]); r = int(sys.argv[4])
    top = int(sys.argv[5]) if len(sys.argv) > 5 else 8
    G = Grp("F", k)
    t0 = time.time()
    dist, layers, elems, I, _ = build(G, R, 0)
    ballr = {x: dv for x, dv in dist.items() if dv <= r}
    res = []
    for h in elems:
        nbrs = [G.mul(h, a) for a in G.S]
        nbrs = [g for g in nbrs if g in dist]
        best = None
        for q in geodesics(G, dist, I, h):
            m = max(D_fixed(G, dist, I, ballr, r, q, g) for g in nbrs)
            if best is None or m < best:
                best = m
                if best <= 1:
                    break
        res.append((best, dist[h], word_of(G, dist, h)))
    res.sort(key=lambda x: -x[0])
    hist = {}
    for x in res:
        hist[x[0]] = hist.get(x[0], 0) + 1
    print("vertex k=%d R=%d r=%d elems=%d hist=%s (%.1fs)" % (k, R, r, len(res), sorted(hist.items()), time.time() - t0))
    for x in res[:top]:
        print("  Dv=%d |h|=%d h=%s" % x)


if __name__ == "__main__":
    if sys.argv[1] == "v":
        vertex_main()
    else:
        main()
