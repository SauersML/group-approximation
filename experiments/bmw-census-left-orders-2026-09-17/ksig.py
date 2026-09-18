# Orbit-signalizer certificate inside the invariant-subtree group K (selfrep.build).
# Edge g -> s: v a vertex of X^* (level <= Lv) with g-orbit of length k >= 1 and s = g^k|_v.  If ord(g) = N is
# finite then k | N and ord(s) <= ord(g^k) = N/k.  Nodes are identified up to conjugacy and inversion in K
# (s ~ t iff s = c t^{+-1} c^-1 for a word c of length <= Lc; checked exactly by selfrep.trivial), which
# preserves orders.  A directed cycle containing an edge of weight k > 1 then gives N <= N/k: some node has
# infinite order, so K is infinite, H_x (which maps onto K) is infinite and Gamma is irreducible
# (Burger-Mozes, Lattices in products of trees, Prop. 1.2).
# usage: ksig.py census.json side Lg Lv Lc maxnodes idx...
import sys, json, itertools
from lo_census import load
from selfrep import build, act_path, trivial, inv
from kkps import words, red

def orbit(K, g, v):
    u, k = act_path(K, g, v)[0], 1
    while u != v and k < 500: u = act_path(K, g, u)[0]; k += 1
    return k if u == v else None

def search(K, g0, Lv, Lc, maxnodes):
    conj = [()] + list(words(K, Lc))
    nodes = [g0]; edges = {}
    def ident(s):
        for j, t in enumerate(nodes):
            for c in conj:
                for te in (t, inv(K, t)):
                    w = red(K, s + c + inv(K, te) + inv(K, c))
                    if not w or trivial(K, w): return j, c, te != t
        return None
    q = 0
    while q < len(nodes) and len(nodes) < maxnodes:
        g = nodes[q]; out = []
        for d in range(1, Lv + 1):
            for v in itertools.product(K['X'], repeat=d):
                k = orbit(K, g, v)
                if k is None: continue
                _, s = act_path(K, g * k, v); s = red(K, s)
                if not s or trivial(K, s): continue
                r = ident(s)
                if r is None:
                    nodes.append(s); r = (len(nodes) - 1, (), False)
                out.append((r[0], k, v, r[1], r[2], s))
        edges[q] = out; q += 1
        # cycle through an edge of weight > 1: j -> ... reachable back
        adj = {a: {e[0] for e in es} for a, es in edges.items()}
        def reach(a, b):
            seen = {a}; st = [a]
            while st:
                x = st.pop()
                if x == b: return True
                for y in adj.get(x, ()):
                    if y not in seen: seen.add(y); st.append(y)
            return False
        for a, es in edges.items():
            for (b, k, v, c, flip, s) in es:
                if k > 1 and reach(b, a):
                    # recover the cycle
                    path = [a]; prev = {b: None}; st = [b]
                    while st:
                        x = st.pop(0)
                        if x == a: break
                        for y in adj.get(x, ()):
                            if y not in prev: prev[y] = x; st.append(y)
                    cyc = [a]; x = a
                    while x != b: x = prev[x]; cyc.append(x)
                    cyc.reverse()
                    return dict(nodes=[list(n) for n in nodes], heavy_edge=dict(frm=a, to=b, k=k, v=v, conj=c, inverted=flip),
                                cycle=cyc, edges={str(x): [(e[0], e[1], e[2], e[3], e[4]) for e in edges[x]] for x in set(cyc)})
    return dict(nodes=len(nodes), cycle=None)

if __name__ == "__main__":
    path, side, Lg, Lv, Lc, mx = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6])
    for i, G in load(path):
        if i in set(map(int, sys.argv[7:])):
            K = build(G, side); res = None
            for g in words(K, Lg):
                if trivial(K, g): continue
                r = search(K, g, Lv, Lc, mx)
                if r.get('cycle'): res = dict(start=g, **r); break
            print(json.dumps(dict(census=path, idx=i, side=side, fixed_letter=K['f'], certificate=res)), flush=True)
