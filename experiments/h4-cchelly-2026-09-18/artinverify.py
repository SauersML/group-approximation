"""Independent check of cchelly lines in type A_{n-1} via the faithful Artin representation B_n -> Aut(F_n).
usage: python3 artinverify.py NAME LOG   (NAME in A3, A4; letters rebuilt exactly as dumpgen.py builds them)
For every HBALL/HCAND line (a, b, u, v) it checks [u,a] = [v,b] != 1 and, for VC failure, [u,b] != k and [v,a] != k."""
import sys, re
sys.path.insert(0, '/home/user/group-approximation/experiments/h4-artin-complex-6cycles-2026-09-17')
from garside import Coxeter
from search import DIAGRAMS
name, log = sys.argv[1], sys.argv[2]
n, md = DIAGRAMS[name]; W = Coxeter(n, md)
full = (1 << n) - 1; X = full & ~1; Y = full & ~(1 << (n - 1)); Z = X & Y
def mer(T):  # identical to dumpgen.py
    order = sorted([w for w in range(W.N) if W.supp[w] & ~T == 0], key=lambda w: (W.length[w], W.word[w]))
    seen = {}
    for w in order:
        for s in range(n):
            if not (T >> s) & 1 or W.length[W.rmul[w][s]] < W.length[w]:
                continue
            r = W.mul(W.rmul[w][s], W.inv[w])
            if r in seen or W.supp[r] & ~Z == 0:
                continue
            seen[r] = [i + 1 for i in W.word[w]] + [s + 1, s + 1] + [-(i + 1) for i in reversed(W.word[w])]
    return list(seen.values())
L = {}
for pre, ws in (('p', mer(Y)), ('x', mer(X))):
    for i, w in enumerate(ws):
        L[f'{pre}{i}'] = w; L[f'{pre}{i}\''] = [-g for g in reversed(w)]
m = n + 1  # strands
def red(x):
    out = []
    for g in x:
        if out and out[-1] == -g: out.pop()
        else: out.append(g)
    return out
def phi(g, t):  # image of letter t (signed strand index) under sigma_|g|^{sign g}
    i = abs(g); s = 1 if t > 0 else -1; a = abs(t)
    if g > 0: img = [i, i + 1, -i] if a == i else [i] if a == i + 1 else [a]
    else: img = [i + 1] if a == i else [-(i + 1), i, i + 1] if a == i + 1 else [a]
    return img if s > 0 else [-h for h in reversed(img)]
def rep(word):
    res = []
    for j in range(1, m + 1):
        x = [j]
        for g in reversed(word):
            x = red([h for t in x for h in phi(g, t)])
        res.append(tuple(x))
    return tuple(res)
def w(s): return [g for tok in s.split() for g in L[tok]]
def inv(x): return [-g for g in reversed(x)]
def comm(u, a): return u + a + inv(u) + inv(a)
ID = rep([])
tot = ok = vcf = 0
for line in open(log):
    if not line.startswith(('HBALL', 'HCAND')): continue
    g = re.search(r'a=(.*?) \| b=(.*?) \|.*\| u=(.*?) \| v=(.*)$', line.rstrip())
    a, b, u, v = (w(g.group(i)) for i in (1, 2, 3, 4))
    k = rep(comm(u, a)); tot += 1
    good = k == rep(comm(v, b)) and k != ID
    ok += good
    vcf += good and rep(comm(u, b)) != k and rep(comm(v, a)) != k
print(f'{name}: {tot} lines, commutator identity confirmed on {ok}, VC failure confirmed on {vcf}')
if len(sys.argv) > 3:  # print the shortest confirmed VC failures and the letters
    for k2 in sorted(L): print(k2, L[k2]) if "'" not in k2 else None
    best = []
    for line in open(log):
        if not line.startswith('HBALL'): continue
        g = re.search(r'a=(.*?) \| b=(.*?) \|.*\| u=(.*?) \| v=(.*)$', line.rstrip())
        a, b, u, v = (w(g.group(i)) for i in (1, 2, 3, 4)); k = rep(comm(u, a))
        if k == rep(comm(v, b)) and rep(comm(u, b)) != k and rep(comm(v, a)) != k:
            best.append((sum(len(g.group(i).split()) for i in (1, 2, 3, 4)), line.strip()))
    for t in sorted(best)[:int(sys.argv[3])]: print(t)
