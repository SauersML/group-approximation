import sys, itertools, collections
import antiflag as AF
B = int(sys.argv[1])
verts = AF.build(B); A, bad = AF.graph(verts)
def pr(i, j): return round(AF.cartan(verts[i], verts[j]) * AF.cartan(verts[j], verts[i]))
hist = collections.Counter(); maxd = 0
for v in range(len(verts)):
    N = sorted(A[v])
    cnt = collections.Counter(pr(a, b) for a, b in itertools.combinations(N, 2) if b not in A[a])
    hist.update(cnt)
    # max clique in "loxodromic compatibility" graph on N
    comp = {a: set(b for b in N if b != a and b not in A[a] and not (0 <= pr(a, b) <= 4)) for a in N}
    best = 0
    def grow(S, cand):
        global best
        best = max(best, len(S))
        for c in list(cand):
            grow(S + [c], cand & comp[c]); cand = cand - {c}
    grow([], set(N))
    maxd = max(maxd, best)
print("B", B, "products among neighbours of a common vertex:", sorted(hist.items()))
print("max number of pairwise loxodromic independent neighbours:", maxd)
