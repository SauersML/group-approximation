# Independent check: homomorphisms Gamma'' -> A5 with t != 1 (x up to conjugacy).
import itertools, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gamma2 import R0, R1
P = [p for p in itertools.permutations(range(5))
     if sum(1 for i in range(5) for j in range(i) if p[j] > p[i]) % 2 == 0]
idx = {p: i for i, p in enumerate(P)}
mul = [[idx[tuple(a[b[k]] for k in range(5))] for b in P] for a in P]   # a∘b
inv = [idx[tuple(sorted(range(5), key=lambda k: a[k]))] for a in P]
e = idx[tuple(range(5))]
def ev(word, im):
    g = e
    for c in word:
        g = mul[g][im[c]]
    return g
reps, seen = [], set()
for a in range(60):
    if a in seen: continue
    reps.append(a)
    for b in range(60): seen.add(mul[mul[b][a]][inv[b]])
found = []
for xi in reps:
    for yi in range(60):
        for ti in range(60):
            if ti == e: continue
            im = {'x': xi, 'X': inv[xi], 'y': yi, 'Y': inv[yi], 't': ti, 'T': inv[ti]}
            if ev(R0, im) == e and ev(R1, im) == e:
                found.append((P[ti], P[xi], P[yi]))
print(len(found), 'homs Gamma\'\' -> A5 with t != 1 (x fixed up to conjugacy)')
for f in found[:3]: print('t,x,y =', f)
