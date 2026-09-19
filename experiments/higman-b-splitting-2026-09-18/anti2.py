"""Section-graph certificates of infinite order for B = <b,d> acting on edges of T_B = A-words.
Nodes: (conjugacy class in B of a cyclically reduced word h, syllable type s in {a,c}).
Edge (h,s) -> (h',s') labelled n: s^x has <h>-orbit of exact size n and the section of h^n at s^x is
conjugate to h' (s' = other type).  A cycle through an edge with n >= 2 gives, by the lemma in
anti.py, a vertex v of even length with orbit size N >= 2 under h whose h^N-section is conjugate to h:
h has infinite order, B/Lambda_B is infinite and Gamma(3,m) is irreducible.
usage: python3 anti2.py e cap maxnodes seedname"""
import sys
e = int(sys.argv[1]); cap = int(sys.argv[2]); maxnodes = int(sys.argv[3]); seed = sys.argv[4]
sys.argv = [sys.argv[0], str(e), '1', '1']
from pathstab import red, inv, m
from anti import left, cyc, section_power, orbit_reps, other


def canon(w):
    c = cyc(w); L = len(c)
    if L == 0: return c
    return min(c[i:] + c[:i] for i in range(L))


SEEDS = {'comm': (('b', m-1), ('d', m-1), ('b', 1), ('d', 1)), 'bd': (('b', 1), ('d', 1)),
         'bdinv': (('b', 1), ('d', m-1)), 'b2d': (('b', 2), ('d', 1)),
         'comm2': (('b', m-2), ('d', m-1), ('b', 2), ('d', 1))}
g0 = canon(SEEDS[seed])
nodes = {}; order = []; edges = {}
todo = [(g0, 'a'), (g0, 'c')]
while todo and len(order) < maxnodes:
    node = todo.pop()
    if node in nodes: continue
    nodes[node] = len(order); order.append(node)
    h, s = node; out = []
    for x in orbit_reps(h, s):
        n, sec = section_power(h, s, x)
        sec = canon(sec)
        if len(sec) == 0 or len(sec) > cap: continue
        tgt = (sec, other[s]); out.append((tgt, n, x))
        if tgt not in nodes: todo.append(tgt)
    edges[node] = out
print('seed', seed, 'e', e, 'nodes explored', len(order), 'frontier', len(todo)); sys.stdout.flush()

# iterative Tarjan SCC on explored nodes
idx = {}; low = {}; onst = set(); st = []; comp = {}; c = 0; counter = 0
for root in order:
    if root in idx: continue
    work = [(root, 0)]
    while work:
        v, i = work.pop()
        if i == 0:
            idx[v] = low[v] = counter; counter += 1; st.append(v); onst.add(v)
        nbrs = [t for (t, n, x) in edges.get(v, []) if t in edges]
        recurse = False
        for j in range(i, len(nbrs)):
            w = nbrs[j]
            if w not in idx:
                work.append((v, j + 1)); work.append((w, 0)); recurse = True; break
            elif w in onst:
                low[v] = min(low[v], idx[w])
        if recurse: continue
        if low[v] == idx[v]:
            while True:
                w = st.pop(); onst.discard(w); comp[w] = c
                if w == v: break
            c += 1
        if work:
            u = work[-1][0]; low[u] = min(low[u], low[v])

found = 0
for v in order:
    for (t, n, x) in edges[v]:
        if n >= 2 and t in comp and comp[t] == comp[v]:
            found += 1
            if found <= 5: print('CERT edge', v, '->', t, 'orbit', n, 'at', x)
print('seed', seed, 'e', e, 'SCCs', c, 'certificate edges', found)
