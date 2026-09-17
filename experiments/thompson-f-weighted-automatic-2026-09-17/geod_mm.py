"""Meet-in-the-middle word length and geodesic enumeration for F over X_k.

usage: geod_mm.py k r word [word ...]
Letters: a/A = x0^{+-1}, b/B = x1, c/C = x2, d/D = x3 (as in geocomb_sat.py).
Lengths up to 2r are exact.  Prints every geodesic word and its x0-exponent
profile chi0(t) (number of a minus number of A in the prefix of length t).
"""
import sys
from geocomb_sat import Grp, build

k = int(sys.argv[1]); r = int(sys.argv[2])
G = Grp("F", k)
dist, layers, elems, I, _ = build(G, r, 0)
names = "aAbBcCdDeE"
S = {names[i]: G.S[i] for i in range(len(G.S))}
INV = {names[i]: names[i ^ 1] for i in range(len(G.S))}
_cache = {}


def length(x):
    v = dist.get(x)
    if v is not None:
        return v
    v = _cache.get(x)
    if v is not None:
        return v
    best = 2 * r + 1
    # x = y z with |y| <= r, |z| <= r ; scan y over layers by increasing length
    for L, lay in enumerate(layers):
        if L >= best:
            break
        for y in lay:
            z = G.mul(G.inv(y), x)
            dz = dist.get(z)
            if dz is not None and L + dz < best:
                best = L + dz
    _cache[x] = best
    return best


def ev(w):
    x = G.id
    for ch in w:
        x = G.mul(x, S[ch])
    return x


def geodesics(g):
    L = length(g)
    out = []

    def rec(u, w):
        t = len(w)
        if t == L:
            if u == g:
                out.append(w)
            return
        for ch, s in S.items():
            if w and INV[ch] == w[-1]:
                continue
            v = G.mul(u, s)
            if length(G.mul(G.inv(v), g)) == L - t - 1:
                rec(v, w + ch)
    rec(G.id, "")
    return L, out


if __name__ == "__main__":
    for w in sys.argv[3:]:
        L, gs = geodesics(ev(w))
        print("%s: length %d, %d geodesics" % (w, L, len(gs)))
        for p in gs:
            prof = [0]
            for ch in p:
                prof.append(prof[-1] + (1 if ch == "a" else -1 if ch == "A" else 0))
            print("   %s  chi0=%s" % (p, prof))
