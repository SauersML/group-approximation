#!/usr/bin/env python3
# samecheck2.py -- (1) extract the letter maps with which the census code's are_same identifies classes 435 and 477
# (t=3, graph 3) and test whether they respect inverses; (2) brute-force isomorphism test between the two
# (vertex permutations x per-vertex half-edge bijections), written independently of fsenum's automorphism routine.
import itertools, collections
import fsac
src = open("Fake-Surfaces/fakesurfaces_cla_6.py").read()
ns = {"permutations": itertools.permutations, "product": itertools.product, "chain": itertools.chain,
      "Counter": collections.Counter}
exec(src[src.index("def sort_surface_longest_disk_to_shortest"):src.index("def remove_duplicate_fake_surfaces")], ns)
exec(src[src.index("def are_compatible"):src.index("graph_four_verts_1")], ns)
S = fsac.Surface(fsac.load_graphs(3)[2]); W1, W2 = S.words(435), S.words(477)
fmt = lambda W: tuple(ns["sort_surface_longest_disk_to_shortest"](tuple(tuple(w) for w in W)))
s1, s2 = fmt(W1), fmt(W2)
# re-run are_same_with_ordering but keep the surviving letter maps
maps = []
for v2 in ns["reorder_disks_of_same_size"](s2):
    dicts = [{}]
    for k in range(len(s1)):
        new = []
        for d in dicts:
            a, b = s1[k], v2[k]
            for x, y in ((a, b), (a, tuple(-z for z in b)), (tuple(-z for z in a), b), (tuple(-z for z in a), tuple(-z for z in b))):
                new += ns["are_compatible"](x, y, d)
        dicts = new
    maps += dicts
print("are_same(435,477) =", ns["are_same"](s1, s2), "| surviving letter maps:", len(maps))
for d in maps[:3]:
    bad = [(x, d[x], d.get(-x)) for x in d if -x in d and d[-x] != -d[x]]
    print("  map", dict(sorted(d.items())), "| inverse-inconsistent pairs:", bad[:6])
# independent isomorphism test on the corner data
def corner_data(code):
    nxt = {}
    for e in range(S.E):
        d = code % 6; code //= 6
        for k in range(3):
            nxt[(2*e, S.oth[2*e][k])] = (2*e+1, S.oth[2*e+1][fsac.P[d][k]])
            nxt[(2*e+1, S.oth[2*e+1][fsac.P[d][k]])] = (2*e, S.oth[2*e][k])
    return nxt       # (half-edge h, other half-edge x at h's vertex) -> same at the partner end
N1, N2 = corner_data(435), corner_data(477)
H = len(S.vert); iso = 0; tried = 0
byv = collections.defaultdict(list)
for h in range(H): byv[S.vert[h]].append(h)
for p in itertools.permutations(range(S.t)):
    for bij in itertools.product(*[list(itertools.permutations(byv[p[v]])) for v in range(S.t)]):
        phi = {}
        for v in range(S.t):
            for h, img in zip(byv[v], bij[v]): phi[h] = img
        if any(phi[h ^ 1] != phi[h] ^ 1 for h in range(H)): continue   # must send edges to edges
        tried += 1
        if all(N2[(phi[h], phi[x])] == (phi[h2], phi[x2]) for (h, x), (h2, x2) in N1.items()): iso += 1
print("edge-preserving half-edge bijections tried:", tried, "| isomorphisms 435 -> 477:", iso)
