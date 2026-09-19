# kchain.py in.jsonl k L : Klein chains through pure words. Nodes: nonempty reduced pure h-words and pure v-words
# of even length <= L (elements of Gamma^+). Edge x -> y when y x y^-1 = x^-1 (y inverts x), tested by the
# rewriting normal form: y x = x^-1 y. A directed cycle refutes left-orderability (Klein-chain criterion:
# y x y^-1 = x^-1 forces |x| < |y|, |g| = max(g, g^-1)). Prints the shortest cycle found, or none.
import sys, json, itertools
from sample import VH
from vh_enum import inv_arr
r = [json.loads(l) for l in open(sys.argv[1])][int(sys.argv[2])]; L = int(sys.argv[3])
m, pA, n, pB = int(r['pat'][0]), int(r['pat'][1]), int(r['pat'][3]), int(r['pat'][4])
G = VH(inv_arr(m, pA), inv_arr(n, pB), {tuple(a): tuple(b) for a, b in r['sq']}); G.confluence()
def words(t, k, inv):
    out = []; lay = [()]
    for d in range(1, L + 1):
        lay = [w + (x,) for w in lay for x in range(k) if not w or inv[w[-1]] != x]
        if d % 2 == 0: out += [tuple((t, x) for x in w) for w in lay]
    return out
def inv(w): return G.rw([(c[0], (G.iA if c[0] == 'h' else G.iB)[c[1]]) for c in reversed(w)])
H = words('h', m, G.iA); V = words('v', n, G.iB)
edges = {}
for x, y in itertools.chain(((x, y) for x in V for y in H), ((x, y) for x in H for y in V)):
    if G.rw(list(y) + list(x)) == G.rw(list(inv(x)) + list(y)): edges.setdefault(x, []).append(y)
print('nodes', len(H) + len(V), 'edges', sum(map(len, edges.values())), flush=True)
best = None                                       # shortest directed cycle by BFS from every node
for s in edges:
    par = {s: None}; q = [s]; found = None
    while q and not found:
        nq = []
        for u in q:
            for w in edges.get(u, []):
                if w == s: found = u; break
                if w not in par: par[w] = u; nq.append(w)
            if found: break
        q = nq
    if found:
        cyc = [found]
        while cyc[-1] != s: cyc.append(par[cyc[-1]])
        cyc = cyc[::-1]
        if best is None or len(cyc) < len(best): best = cyc
print(json.dumps(dict(pat=r['pat'], seed=r['seed'], L=L, cycle=[''.join('%s%d' % c for c in w) for w in best] if best else None)))
