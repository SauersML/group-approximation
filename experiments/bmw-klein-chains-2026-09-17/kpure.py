# Klein-chain scan restricted to pure words: V-words (even length <= L) and H-words (even length <= L) of Gamma^+.
# Edge b -> a means a inverts b (a b a^-1 = b^-1); in Gamma^+ such edges only join a V-word and an H-word
# (a nontrivial element of a free group is never conjugate to its inverse).
#  a in V, b in H:  b^-1 a = a b      <=> the H-word b^-1 pushed rightward through a gives output a and section b.
#  a in H, b in V:  b a^-1 = a^-1 b^-1 <=> the V-word b pushed rightward through a^-1 gives output a^-1, section b^-1.
# Squares: SQ(h, v) = (v', h') means h v = v' h'; hence also v h = h' v' (all letters are involutions).
# usage: kpure.py census.json L out.jsonl classes
import sys, json
sys.setrecursionlimit(100000)
D = json.load(open(sys.argv[1])); L = int(sys.argv[2]); out = open(sys.argv[3], 'a')
assert D['pA'] == 0 and D['pB'] == 0
m, n = D['m'], D['n']          # m horizontal letters, n vertical letters
def words(a):
    o = [()]; res = []
    for k in range(L):
        o = [w + (c,) for w in o for c in range(a) if not w or w[-1] != c]
        if (k + 1) % 2 == 0: res += o
    return res
for ci in [int(c) for c in sys.argv[4].split(',')]:
    SQ = {tuple(a): tuple(b) for a, b in D['reps'][ci]}
    HV = {}   # (h, v) -> (v', h'):  h v = v' h'
    VH = {}   # (v, h) -> (h', v'):  v h = h' v'
    for (h, v), (v2, h2) in SQ.items(): HV[(h, v)] = (v2, h2); VH[(v, h)] = (h2, v2)
    def push_h_through_v(x, a):      # x (H-word) * a (V-word) = a' x'
        x = list(x); outv = []
        for v in a:
            for i in range(len(x) - 1, -1, -1):
                v, x[i] = HV[(x[i], v)]
            outv.append(v)
        return tuple(outv), tuple(x)
    def fixed(x, T, alpha):  # all even words a (len<=L) in alphabet alpha with x a = a x' ; returns list (a, x')
        res = []
        def dfs(a, sec):
            if a and len(a) % 2 == 0: res.append((a, tuple(sec)))
            if len(a) == L: return
            for c in range(alpha):
                if a and a[-1] == c: continue
                s = list(sec); y = c
                for i in range(len(s) - 1, -1, -1):
                    y, s[i] = T[(s[i], y)]
                if y == c: dfs(a + (c,), s)
        dfs((), x); return res
    Hw, Vw = words(m), words(n)
    adj = {}
    for x in Hw:                     # x = b^-1, b in H
        b = tuple(reversed(x))
        for a, sec in fixed(x, HV, n):
            if sec == b: adj.setdefault(('h', b), []).append(('v', a))
    for b in Vw:                     # V-word b pushed through a^-1
        for ai, sec in fixed(b, VH, m):
            if sec == tuple(reversed(b)): adj.setdefault(('v', b), []).append(('h', tuple(reversed(ai))))
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
    def fmt(z): return ('v' + ''.join(map(str, z[1])) + '|h') if z[0] == 'v' else ('v|h' + ''.join(map(str, z[1])))
    rec = {'class': ci, 'L': L, 'pure': True, 'pairs': sum(len(v) for v in adj.values()), 'cycle': [fmt(z) for z in cyc] if cyc else None}
    out.write(json.dumps(rec) + '\n'); out.flush(); print(rec, flush=True)
