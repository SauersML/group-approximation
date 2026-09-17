"""Scan the ball B_R of F over X_k for seesaw elements (Cleary-Taback Def. 4.1) w.r.t. x0.

usage: seesaw_scan.py k R [top]
swing(w) = min(s+, s-), s+ = largest l with |w x0^j| = |w| - j (j <= l) and, for 0 <= m < l,
the only generators reducing |w x0^m| are x0 (and x0^-1 when m = 0).  Exact inside B_R.
"""
import sys, time
from geocomb_sat import Grp, word_of


def bfs(G, R):
    dist = {G.id: 0}
    lay = [G.id]
    for L in range(1, R + 1):
        nxt = []
        for g in lay:
            for s in G.S:
                h = G.mul(g, s)
                if h not in dist:
                    dist[h] = L
                    nxt.append(h)
        lay = nxt
    return dist


def main():
    k = int(sys.argv[1]); R = int(sys.argv[2]); top = int(sys.argv[3]) if len(sys.argv) > 3 else 10
    G = Grp("F", k)
    t0 = time.time()
    dist = bfs(G, R)
    BIG = R + 1
    L = lambda x: dist.get(x, BIG)
    a, A = G.S[0], G.S[1]

    def reducers(x):
        return [i for i, s in enumerate(G.S) if L(G.mul(x, s)) < L(x)]

    res = []
    for w, n in dist.items():
        if n < 2 or reducers(w) != [0, 1]:
            continue
        sw = []
        for gi, g in ((0, a), (1, A)):
            x, l = w, 0
            while True:
                y = G.mul(x, g)
                if L(y) != L(x) - 1:
                    break
                l += 1
                x = y
                if reducers(x) != [gi]:
                    break
            sw.append(l)
        res.append((min(sw), n, word_of(G, dist, w)))
    res.sort(key=lambda t: (-t[0], t[1]))
    hist = {}
    for t in res:
        hist[t[0]] = hist.get(t[0], 0) + 1
    print("k=%d R=%d |B_R|=%d seesaw-candidates hist(swing)=%s (%.1fs)" % (k, R, len(dist), sorted(hist.items()), time.time() - t0))
    for t in res[:top]:
        print("  swing=%d |w|=%d w=%s" % t)


if __name__ == "__main__":
    main()
