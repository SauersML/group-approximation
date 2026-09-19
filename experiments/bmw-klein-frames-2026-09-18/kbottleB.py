# Flat Klein bottles, the other bound: all pure pairs A B A^-1 = B^-1 with |B| = q FIXED and |A| UNBOUNDED.
# B is a reduced word of family F (v by default, h with --swap), A a reduced word of the other family, both even.
# A B A^-1 = B^-1  <=>  B A = A B^-1  <=>  pushing A letter by letter through B returns every letter unchanged
# (output A) and leaves the section B^-1.  States (s, last letter of A, parity of |A|), s a word of length q:
# a finite graph.  A pair with |B| = q exists iff some state (B, -, 0) reaches (B^-1, c, 0) by >= 1 step;
# reachability to the targets is computed exactly on the condensation (bitsets), so the result is complete
# for every |A|.
# usage: kbottleB.py census.json class Q [--swap]     (Q: max even |B|)
import sys, json
D = json.load(open(sys.argv[1])); ci = int(sys.argv[2]); QM = int(sys.argv[3]); SW = '--swap' in sys.argv
m, n, iA, iB = D['m'], D['n'], D['iA'], D['iB']
SQ = {tuple(a): tuple(b) for a, b in D['reps'][ci]}                  # h v = v' h'
VH = {}
for (h, v), (v2, h2) in SQ.items(): VH[(iB[v2], h)] = (h2, iB[v])   # v h = h' v'
if SW: T, nb, ilB, na, ilA = SQ, m, iA, n, iB        # B an h-word, A a v-word: T[(h, v)] = (v', h')
else:  T, nb, ilB, na, ilA = VH, n, iB, m, iA        # B a v-word, A an h-word: T[(v, h)] = (h', v')
def push(s, c):                                      # s c = c' s'
    s = list(s)
    for i in range(len(s) - 1, -1, -1): c, s[i] = T[(s[i], c)]
    return c, tuple(s)
def winv(w, il): return tuple(il[c] for c in reversed(w))
sys.setrecursionlimit(10000)
for q in range(2, QM + 1, 2):
    W = [()]
    for _ in range(q): W = [w + (c,) for w in W for c in range(nb) if not w or w[-1] != ilB[c]]
    fix = {}                                         # s -> list of (c, s') with s c = c s'
    for s in W:
        fix[s] = [(c, s2) for c in range(na) for (c2, s2) in [push(s, c)] if c2 == c]
    nodes = [(s, l, p) for s in W for l in range(-1, na) for p in (0, 1)]
    ix = {u: i for i, u in enumerate(nodes)}
    adj = [[] for _ in nodes]
    for (s, l, p), i in ix.items():
        for c, s2 in fix[s]:
            if l >= 0 and c == ilA[l]: continue
            adj[i].append(ix[(s2, c, 1 - p)])
    tgt = {ix[(winv(s, ilB), c, 0)]: k for k, s in enumerate(W) for c in range(na)}
    # iterative Tarjan, then bitset propagation in reverse topological order
    N = len(nodes); idx = [-1] * N; low = [0] * N; on = [False] * N; comp = [-1] * N; st = []; cnt = 0; order = []
    for r in range(N):
        if idx[r] >= 0: continue
        work = [(r, 0)]; idx[r] = low[r] = cnt; cnt += 1; st.append(r); on[r] = True
        while work:
            v, k = work[-1]
            if k < len(adj[v]):
                work[-1] = (v, k + 1); w = adj[v][k]
                if idx[w] < 0: idx[w] = low[w] = cnt; cnt += 1; st.append(w); on[w] = True; work.append((w, 0))
                elif on[w]: low[v] = min(low[v], idx[w])
            else:
                work.pop()
                if work: low[work[-1][0]] = min(low[work[-1][0]], low[v])
                if low[v] == idx[v]:
                    cc = []
                    while True:
                        w = st.pop(); on[w] = False; comp[w] = len(order); cc.append(w)
                        if w == v: break
                    order.append(cc)                 # components come out in reverse topological order
    reach = [0] * len(order)                         # bit k: can reach target of word W[k] in >= 0 steps
    for c_id, cc in enumerate(order):
        b = 0
        for v in cc:
            if v in tgt: b |= 1 << tgt[v]
            for w in adj[v]: b |= reach[comp[w]]
        reach[c_id] = b
    found = []
    for k, s in enumerate(W):                        # start (s, -1, 0): need >= 1 step, then reach (s^-1, c, 0)
        for w in adj[ix[(s, -1, 0)]]:
            if reach[comp[w]] >> k & 1: found.append(''.join(map(str, s))); break
    print(json.dumps({'class': ci, 'swap': SW, 'q': q, 'states': N, 'pairs': len(found), 'B': found[:5]}), flush=True)
