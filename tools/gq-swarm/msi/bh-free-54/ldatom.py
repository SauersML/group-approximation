# LD_atom test: if an O_E-dissection D of Delta respects the cut plane x_i = x_j of an atom
# (no piece straddles it), is D >=_E E_ij (restriction to each half hierarchical in the half's frame)?
# Also: plane lemma check (greedy resolution of random rational planes terminates).
import sys, json, time, random
from ore import *
N = int(sys.argv[1])
t0 = time.time()
atoms = []
for (i, j) in ((0, 1), (0, 2), (1, 2)):
    for s in splits(DELTA):
        pass
S = splits(DELTA)   # three atoms, as pairs of halves
def side(v, i, j): return v[i] - v[j]
tested = viol = 0; example = None
for D in up(frozenset([DELTA]), N):
    if len(D) < 2: continue
    for (i, j), (H1, H2) in zip(((0, 1), (0, 2), (1, 2)), S):
        # which atom plane does this pair of halves correspond to? determine by the midpoint
        pass
    for (H1, H2) in S:
        g1 = frozenset(p for p in D if all(inside(x, H1) for x in p))
        g2 = frozenset(p for p in D if all(inside(x, H2) for x in p))
        if len(g1) + len(g2) != len(D): continue       # D does not respect this atom plane
        tested += 1
        if not (hier(H1, g1) and hier(H2, g2)):
            viol += 1
            if example is None: example = (sorted(D), H1, H2)
# plane lemma: greedy on random forms
def resolve(frame, lam, depth=0):
    pos = [k for k in range(3) if lam[k] > 0]; neg = [k for k in range(3) if lam[k] < 0]
    if not pos or not neg: return 1, depth
    # odd vertex = the side with one vertex; crossed edges (odd, other)
    odd = pos[0] if len(pos) == 1 else neg[0]
    others = [k for k in range(3) if k != odd and lam[k] != 0 and (lam[k] > 0) != (lam[odd] > 0)]
    k = max(others, key=lambda q: abs(lam[q]))
    a, b = odd, k
    l1 = list(lam); l1[b] = lam[a] + lam[b]      # child containing vertex a
    l2 = list(lam); l2[a] = lam[a] + lam[b]      # child containing vertex b
    n1, d1 = resolve(None, l1, depth + 1); n2, d2 = resolve(None, l2, depth + 1)
    return n1 + n2, max(d1, d2)
rnd = random.Random(7); worst = 0; worst_leaves = 0; ntests = 0
for _ in range(20000):
    lam = [rnd.randint(-60, 60) for _ in range(3)]
    if not (any(x > 0 for x in lam) and any(x < 0 for x in lam)): continue
    leaves, d = resolve(None, lam); ntests += 1
    worst = max(worst, d); worst_leaves = max(worst_leaves, leaves)
print(json.dumps({"N": N, "LD_atom_instances_tested": tested, "violations": viol,
                  "example": example if example is None else [list(map(list, t)) for t in example[0]],
                  "plane_lemma_random_forms": ntests, "max_depth": worst, "max_leaves": worst_leaves,
                  "secs": round(time.time() - t0, 1)}))
