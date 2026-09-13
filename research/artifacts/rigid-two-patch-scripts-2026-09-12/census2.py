import itertools
# Rigid unbalanced two-patch ternary rules with injective diagonal: blind-pair classes and free-memory two-site moves.
Y = list(itertools.product(range(3), repeat=3))
PAIRS = [(0, 1), (0, 2), (1, 2)]
def rule(c, p, q, tp, tq):
    def mu(y):
        v = (c[0] * y[0] + c[1] * y[1] + c[2] * y[2]) % 3
        if y == p: v = (v + tp) % 3
        if y == q: v = (v + tq) % 3
        return v
    return mu
def put(ctx, i, u):
    y = list(ctx); y.insert(i, u); return tuple(y)
def blind(mu, i):
    out = set()
    for u, v in PAIRS:
        for ctx in itertools.product(range(3), repeat=2):
            if mu(put(ctx, i, u)) == mu(put(ctx, i, v)):
                out.add((u, v)); break
    return out
def classify(c, p, q, tp, tq):
    mu = rule(c, p, q, tp, tq)
    counts = [sum(1 for y in Y if mu(y) == k) for k in range(3)]
    diag_inj = len({mu((v, v, v)) for v in range(3)}) == 3
    B = [blind(mu, i) for i in range(3)]
    rigid = not (B[0] & B[1] & B[2])
    double = [(i, j) for i, j in [(0, 1), (0, 2), (1, 2)] if B[i] & B[j]]
    shapes = []
    for m, m2 in [(0, 1), (0, 2), (1, 2)]:
        third = 3 - m - m2
        o1 = [k for k in range(3) if k != m]; o2 = [k for k in range(3) if k != m2]
        Ps = B[o1[0]] & B[o1[1]]; Pt = B[o2[0]] & B[o2[1]]
        found = False
        for (u0, u1) in Ps:
            for (v0, v1) in Pt:
                for (u, u2) in [(u0, u1), (u1, u0)]:
                    for z in range(3):
                        y = [0, 0, 0]; y2 = [0, 0, 0]
                        y[m], y2[m] = u, u2; y[m2], y2[m2] = v0, v1; y[third] = y2[third] = z
                        if mu(tuple(y)) == mu(tuple(y2)):
                            found = True
        if found:
            shapes.append((m, m2))
    if not double:
        cls = 'II'
    elif shapes:
        cls = 'I-shapes%d' % len(shapes)
    else:
        cls = 'I-noshape-doubles%d' % len(double)
    return counts, diag_inj, rigid, cls, [sorted(b) for b in B]
print('mu3  ', classify((1, 1, 2), (0, 0, 2), (1, 2, 0), 1, 1))
print("mu'  ", classify((1, 1, 2), (0, 1, 0), (1, 2, 2), 1, 2))
print('mu2  ', classify((1, 2, 1), (0, 1, 2), (1, 2, 0), 1, 1))
stats = {}; examples = {}
for c in [(1, 1, 2), (1, 1, 0)]:
    for p, q in itertools.combinations(Y, 2):
        if not set(p) & set(q):
            continue
        for tp, tq in itertools.product((1, 2), repeat=2):
            counts, diag_inj, rigid, cls, B = classify(c, p, q, tp, tq)
            if counts == [9, 9, 9] or not rigid:
                continue
            key = (c, 'diag-injective' if diag_inj else 'diag-collapses', cls)
            stats[key] = stats.get(key, 0) + 1
            examples.setdefault(key, (p, q, tp, tq, counts, B))
for key in sorted(stats):
    print(key, stats[key], 'example', examples[key])
