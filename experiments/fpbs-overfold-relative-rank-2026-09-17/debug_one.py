"""Debug: seed counts and lawful-closure of all lawful seeds for one Cayley action."""
import sys
from struct_search import cayley, seeds_of
from foldlib import depth_graphs, closure, contains_kernel, equals_kernel

j = int(sys.argv[1])
al = tuple(int(x) for x in sys.argv[2].split(','))
be = tuple(int(x) for x in sys.argv[3].split(','))
PA, PB = cayley(al, be, 10 ** 6)
Gj, G, m = depth_graphs(PA, PB, j)
allp, lawp = seeds_of(G, m)
print('V', G.V, Gj.V, 'seeds all/law', len(allp), len(lawp))
cls = closure(G, lawp)
print('all lawful seeds: contains ker', contains_kernel(G, cls, m),
      'equals ker', equals_kernel(G, cls, m), 'classes', len(set(cls)))
comp = {}
for v in range(G.V):
    comp.setdefault(v, v)
# number of connected components of G
par = list(range(G.V))


def f(x):
    while par[x] != x:
        x = par[x]
    return x


for v in range(G.V):
    for k, u in G.nb[v].items():
        par[f(u)] = f(v)
print('components of Gamma_{j+1}', len({f(v) for v in range(G.V)}))
par2 = list(range(Gj.V))
for v in range(Gj.V):
    for k, u in Gj.nb[v].items():
        a, b = v, u
        while par2[a] != a:
            a = par2[a]
        while par2[b] != b:
            b = par2[b]
        par2[b] = a
roots = set()
for v in range(Gj.V):
    a = v
    while par2[a] != a:
        a = par2[a]
    roots.add(a)
print('components of Gamma_j', len(roots))
