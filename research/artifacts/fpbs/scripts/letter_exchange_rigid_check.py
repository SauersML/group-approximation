# Checks for research/fpbs-letter-exchange-nonunimodular-proof.md and for Section 3 of
# research/artifacts/fpbs-f2xz-all-generating-sets-2026-09-12.md (rigid decorations).
# Run: python3 letter_exchange_rigid_check.py  (a few seconds; run on MSI 2026-09-12).
# Expected output:
#   * exchange lifts: 0 bad edges in every positive case;
#   * rigid control D_a={0,1,3}, D_b={0,1,4}: a positive count for every shift, in both modes;
#   * edge-indexed graph A: index sums 2/2 at every vertex, and the unimodularity equations inconsistent;
#   * rigid example: vertical edges in exactly 4 triangles, horizontal edges in 0 or 2;
#   * rigid type maps: only identity (sign +1) and reverse-every-letter (sign -1).
import random
from collections import Counter

LET = ['a', 'A', 'b', 'B']
def inv(x): return x.swapcase()
def mul(w, x): return w[:-1] if w and w[-1] == inv(x) else w + x

def ball(R):
    words, frontier = [''], ['']
    for _ in range(R):
        frontier = [w + x for w in frontier for x in LET if not (w and w[-1] == inv(x))]
        words += frontier
    return words

def Dof(D, t):
    return set(D[t]) if t.islower() else {-d for d in D[t.lower()]}

# ---------- 1. exchange lifts ----------
# classes: two lists of letters; an automorphism maps each letter at a vertex to a letter of the
# same class.  translate mode: out-class {a,b}, in-class {A,B}; reflected mode: {a,B}, {A,b}.
def random_aut(R, classes):
    cls = {t: i for i, C in enumerate(classes) for t in C}
    def rand_perm(C):
        return dict(zip(C, random.sample(C, len(C))))
    img = {'': ''}
    m = {}
    for C in classes:
        m.update(rand_perm(C))
    lm = {'': m}
    for w in ball(R):
        if not w:
            continue
        p, x = w[:-1], w[-1]
        y = lm[p][x]
        assert cls[x] == cls[y]
        img[w] = mul(img[p], y)
        m = {inv(x): inv(y)}
        i = cls[inv(x)]
        assert cls[inv(y)] == i
        others = [t for t in classes[i] if t != inv(x)]
        targets = [t for t in classes[i] if t != inv(y)]
        m.update(dict(zip(others, random.sample(targets, len(targets)))))
        for j, C in enumerate(classes):
            if j != i:
                m.update(rand_perm(C))
        lm[w] = m
    return img, lm

def potential(R, lm, tau):
    h = {'': 0}
    for w in ball(R):
        if not w:
            continue
        p, x = w[:-1], w[-1]
        h[w] = h[p] + tau[lm[p][x]] - tau[x]
    return h

def check_exchange(D, classes, tau, R=5, trials=40, seed=20260912):
    random.seed(seed)
    bad, exchanged = 0, 0
    words = ball(R)
    for _ in range(trials):
        img, lm = random_aut(R, classes)
        h = potential(R, lm, tau)
        for g in words:
            for s in 'ab':
                gs = mul(g, s)
                if len(gs) > R:
                    continue
                t = next(z for z in LET if mul(img[g], z) == img[gs])
                if t.lower() != s:
                    exchanged += 1
                allowed = Dof(D, t)
                bad += sum(1 for d in D[s] if d + h[gs] - h[g] not in allowed)
    return bad, exchanged

TRANS = [['a', 'b'], ['A', 'B']]
REFL = [['a', 'B'], ['A', 'b']]
def tau_for(c): return {'a': 0, 'A': 0, 'b': c, 'B': -c}

positive = [
    ("translate D_a=D_b={0,1,3}, c=0", {'a': [0, 1, 3], 'b': [0, 1, 3]}, TRANS, 0),
    ("translate D_a={0,1,3}, D_b={5,6,8}, c=5", {'a': [0, 1, 3], 'b': [5, 6, 8]}, TRANS, 5),
    ("reflected D_a={0,1,3}, D_b=3-D_a={0,2,3}", {'a': [0, 1, 3], 'b': [0, 2, 3]}, REFL, 3),
    ("reflected D_a={0,2,7}, D_b=8-D_a={1,6,8}", {'a': [0, 2, 7], 'b': [1, 6, 8]}, REFL, 8),
]
for name, D, classes, c in positive:
    bad, ex = check_exchange(D, classes, tau_for(c))
    print(f"exchange {name}: bad edges = {bad}, exchanged edge images = {ex}")

rigid = {'a': [0, 1, 3], 'b': [0, 1, 4]}
for mode, classes in (("translate", TRANS), ("reflected", REFL)):
    counts = [check_exchange(rigid, classes, tau_for(c), R=4, trials=20, seed=7)[0] for c in range(-6, 7)]
    print(f"control rigid {mode}, shifts -6..6: bad edges = {counts}, all positive = {all(x > 0 for x in counts)}")

# ---------- 2. edge-indexed graph A of the exchange proof ----------
A = [('e1', 'u', 'w', 2, 1), ('e2', 'w', 'x', 1, 2), ('e3', 'x', 'w', 1, 1),
     ('e4', 'x', 'u', 1, 1), ('e5', 'w', 'u', 1, 1)]
for v in 'uwx':
    out_sum = sum(ti for (_, t, _, ti, _) in A if t == v)
    in_sum = sum(hi for (_, _, hd, _, hi) in A if hd == v)
    print(f"A vertex {v}: tail-index sum = {out_sum}, head-index sum = {in_sum}")
N, ok = {'u': 1.0}, True
changed = True
while changed:
    changed = False
    for (_, t, hd, ti, hi) in A:
        if t in N and hd not in N:
            N[hd] = N[t] * ti / hi; changed = True
        elif hd in N and t not in N:
            N[t] = N[hd] * hi / ti; changed = True
for (e, t, hd, ti, hi) in A:
    if abs(N[t] * ti - N[hd] * hi) > 1e-9:
        ok = False
        print(f"A unimodularity equation fails on {e}: N({t})*{ti} = {N[t]*ti} vs N({hd})*{hi} = {N[hd]*hi}")
print(f"A unimodular = {ok}; modular product around w -(e2)-> x -(e3)-> w = {(1/2)*(1/1)}")

# ---------- 3. rigid example: triangle counts ----------
def triangle_census(D, V=(1,), R=3, M=12, core_R=1, core_M=4):
    words = ball(R)
    wset = set(words)
    adj = {}
    def add(x, y):
        adj.setdefault(x, set()).add(y); adj.setdefault(y, set()).add(x)
    for g in words:
        for m in range(-M, M + 1):
            for v in V:
                if -M <= m + v <= M:
                    add((g, m), (g, m + v))
            for s in 'ab':
                gs = mul(g, s)
                if gs in wset:
                    for d in D[s]:
                        if -M <= m + d <= M:
                            add((g, m), (gs, m + d))
    census = Counter()
    for g in words:
        if len(g) > core_R:
            continue
        for m in range(-core_M, core_M + 1):
            x = (g, m)
            for y in adj[x]:
                kind = 'vertical' if y[0] == g else 'horizontal'
                census[(kind, len(adj[x] & adj[y]))] += 1
    return census
print("rigid triangle census (kind, triangles): edge-end count =", sorted(triangle_census(rigid).items()))

# ---------- 4. rigid example: allowed type maps ----------
def shape(S): m = min(S); return tuple(sorted(d - m for d in S))
types = LET
maps = {+1: [], -1: []}
for eps in (+1, -1):
    for t in types:
        for t2 in types:
            if shape({eps * d for d in Dof(rigid, t)}) == shape(Dof(rigid, t2)):
                maps[eps].append((t, t2))
print("rigid type maps with sign +1:", maps[+1])
print("rigid type maps with sign -1:", maps[-1])
print("CHECK_DONE")
