# Klein-chain scan on pure words for BMW census classes of ANY pattern mpA_npB (letters may come in
# transposed pairs x, x^-1 = iA[x] / iB[x]).  Generalises ../bmw-klein-chains-2026-09-17/kpure.py.
# Pure words: freely reduced V-words and H-words of even length <= L (they lie in Gamma^+).
# Edge b -> a means a inverts b (a b a^-1 = b^-1).  Such edges only join a V-word and an H-word:
# the even words of one family form a torsion-free subgroup of a free product of cyclic groups, hence a
# free group (Kurosh), in which no nontrivial element is conjugate to its inverse.
#  a in V, b in H:  b^-1 a = a b        <=> H-word b^-1 pushed right through a gives output a, section b.
#  a in H, b in V:  b a^-1 = a^-1 b^-1  <=> V-word b pushed right through c = a^-1 gives output c, section b^-1.
# Squares: SQ(h, v) = (v', h') means h v = v' h'; then v'^-1 h = h' v^-1, i.e. VH(iB[v'], h) = (h', iB[v]).
# With --powers also adds power edges x -> x^k (k >= 2; |x| <= |x^k| in any left order), so that a cycle
# through at least one inverting edge still refutes left-orderability (Promislow-type chains).
# usage: kpure2.py census.json L out.jsonl classes|all|cand [--cand out_X.jsonl] [--powers]
import sys, json
sys.setrecursionlimit(100000)
D = json.load(open(sys.argv[1])); L = int(sys.argv[2]); out = open(sys.argv[3], 'a')
m, n, iA, iB = D['m'], D['n'], D['iA'], D['iB']
sel = sys.argv[4]
if sel == 'all': todo = range(len(D['reps']))
elif sel == 'cand':
    recs = [json.loads(l) for l in open(sys.argv[sys.argv.index('--cand') + 1])]
    todo = [r['idx'] for r in recs if r.get('finH') is None or r.get('finV') is None]
else: todo = [int(c) for c in sel.split(',')]
def words(a, inv):
    o = [()]; res = []
    for k in range(L):
        o = [w + (c,) for w in o for c in range(a) if not w or w[-1] != inv[c]]
        if (k + 1) % 2 == 0: res += o
    return res
def winv(w, inv): return tuple(inv[c] for c in reversed(w))
Hw, Vw = words(m, iA), words(n, iB)
POW = '--powers' in sys.argv
def powkey(z):
    # z = (family, w), w a nonempty even reduced word.  Write w = u c u^-1 (c cyclically reduced),
    # c = p^e with p string-primitive, rho = p^j with j = 1 or 2 the least with |p^j| even; w = u rho^k u^-1.
    # Key: the element u rho u^-1 up to inversion; returns (key, k).
    f, w = z; inv = iA if f == 'h' else iB
    w = list(w); u = []
    while len(w) >= 2 and w[0] == inv[w[-1]]:
        u.append(w[0]); w = w[1:-1]
    c = tuple(w); N = len(c); u = tuple(u)
    p = next(c[:d] for d in range(1, N + 1) if N % d == 0 and c == c[:d] * (N // d))
    j = 1 if len(p) % 2 == 0 else 2
    k = N // (len(p) * j)
    r = u + p * j + winv(u, inv)
    return (f, min(r, winv(r, inv))), k
for ci in todo:
    SQ = {tuple(a): tuple(b) for a, b in D['reps'][ci]}
    HV = dict(SQ)                                   # (h, v) -> (v', h'):  h v = v' h'
    VH = {}                                         # (v, h) -> (h', v'):  v h = h' v'
    for (h, v), (v2, h2) in SQ.items(): VH[(iB[v2], h)] = (h2, iB[v])
    assert len(VH) == m * n
    def fixed(x, T, alpha, inv):  # even reduced words a (len<=L) over alpha with x a = a x'; list of (a, x')
        res = []
        def dfs(a, sec):
            if a and len(a) % 2 == 0: res.append((a, tuple(sec)))
            if len(a) == L: return
            for c in range(alpha):
                if a and a[-1] == inv[c]: continue
                s = list(sec); y = c
                for i in range(len(s) - 1, -1, -1):
                    y, s[i] = T[(s[i], y)]
                if y == c: dfs(a + (c,), s)
        dfs((), x); return res
    adj = {}
    for b in Hw:                     # x = b^-1
        x = winv(b, iA)
        for a, sec in fixed(x, HV, n, iB):
            if sec == b: adj.setdefault(('h', b), []).append(('v', a))
    for b in Vw:                     # V-word b pushed through c = a^-1
        bi = winv(b, iB)
        for c, sec in fixed(b, VH, m, iA):
            if sec == bi: adj.setdefault(('v', b), []).append(('h', winv(c, iA)))
    rep = {}
    if POW:  # nodes become classes {x, x^-1} (|x| = |x^-1|); power edges |r^k| <= |r^k'| for 0 < k < k'
        cls = {}
        for z in set(adj) | {w for ws in adj.values() for w in ws}:
            cls[z] = powkey(z); rep.setdefault(cls[z], z)
        adj = {cls[b]: sorted(set(cls[a] for a in ws)) for b, ws in adj.items()}
        grp = {}
        for c in rep: grp.setdefault(c[0], []).append(c)
        for key, lst in grp.items():
            lst.sort(key=lambda c: c[1])
            for c1, c2 in zip(lst, lst[1:]): adj.setdefault(c1, []).append(c2)
    color = {}; stack = []
    def dfs(u):
        color[u] = 1; stack.append(u)
        for w in adj.get(u, []):
            if color.get(w) == 1: return stack[stack.index(w):]
            if w not in color:
                c = dfs(w)
                if c: return c
        color[u] = 2; stack.pop(); return None
    cyc = None
    for u in list(adj):
        if u not in color:
            cyc = dfs(u)
            if cyc: break
    def fmt(z):
        if POW: z = rep[z]
        return ('v' + ''.join(map(str, z[1])) + '|h') if z[0] == 'v' else ('v|h' + ''.join(map(str, z[1])))
    rec = {'class': ci, 'L': L, 'pure': True, 'powers': POW, 'pairs': sum(len(v) for v in adj.values()),
           'cycle': [fmt(z) for z in cyc] if cyc else None}
    out.write(json.dumps(rec) + '\n'); out.flush(); print(rec, flush=True)
