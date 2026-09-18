# Scan census classes for a Klein chain: elements x_1..x_m of Gamma^+ with x_{i+1} x_i x_{i+1}^-1 = x_i^-1 (indices mod m).
# In a left order, a b a^-1 = b^-1 (b != 1) forces |b| < |a|, so such a cycle refutes left-orderability of Gamma^+.
# usage: kscan.py census.json L out.jsonl [classes]
import sys, json
sys.setrecursionlimit(100000)
from lo_census import VH
D = json.load(open(sys.argv[1])); L = int(sys.argv[2]); out = open(sys.argv[3], 'a')
assert D['pA'] == 0 and D['pB'] == 0, 'involution patterns only'
m, n = D['m'], D['n']      # census convention: m horizontal letters (iA), n vertical letters (iB); SQ keys are (h, v)
todo = [int(c) for c in sys.argv[4].split(',')] if len(sys.argv) > 4 else range(len(D['reps']))
def words(k, a):
    o = [()]
    for _ in range(k): o = [w + (c,) for w in o for c in range(a) if not w or w[-1] != c]
    return o
Vw = [w for k in range(0, L + 1, 2) for w in words(k, n)]
Hw = [w for k in range(0, L + 1, 2) for w in words(k, m)]
E = [(a, b) for a in Vw for b in Hw if 0 < len(a) + len(b) <= L]
for ci in todo:
    SQ = {tuple(a): tuple(b) for a, b in D['reps'][ci]}
    G = VH(list(range(m)), list(range(n)), SQ); G.confluence(); M = G.mul   # all letters are involutions
    def inv(z): return M(((), tuple(reversed(z[1]))), (tuple(reversed(z[0])), ()))
    IV = {z: inv(z) for z in E}
    adj = {}
    for b in E:
        for a in E:
            if M(a, b) == M(IV[b], a): adj.setdefault(b, []).append(a)   # a inverts b: |b| < |a|
    color = {}; stack = []; cyc = None
    def dfs(u):
        color[u] = 1; stack.append(u)
        for w in adj.get(u, []):
            if color.get(w) == 1: return stack[stack.index(w):]
            if w not in color:
                c = dfs(w)
                if c: return c
        color[u] = 2; stack.pop(); return None
    for u in list(adj):
        if u not in color:
            cyc = dfs(u)
            if cyc: break
    rec = {'class': ci, 'L': L, 'pairs': sum(len(v) for v in adj.values()),
           'cycle': [['v' + ''.join(map(str, z[0])), 'h' + ''.join(map(str, z[1]))] for z in cyc] if cyc else None}
    out.write(json.dumps(rec) + '\n'); out.flush()
