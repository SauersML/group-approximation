import itertools
# Rigid unbalanced two-patch ternary rules: blind-pair classes and free-memory two-site moves.
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
stats = {}
examples = {}
for c in [(1, 1, 2), (1, 1, 0)]:
    for p, q in itertools.combinations(Y, 2):
        if not set(p) & set(q):
            continue
        for tp, tq in itertools.product((1, 2), repeat=2):
            mu = rule(c, p, q, tp, tq)
            counts = [sum(1 for y in Y if mu(y) == k) for k in range(3)]
            if counts == [9, 9, 9]:
                continue
            B = [blind(mu, i) for i in range(3)]
            if B[0] & B[1] & B[2]:
                continue  # not rigid
            double = [(i, j) for i, j in [(0, 1), (0, 2), (1, 2)] if B[i] & B[j]]
            if not double:
                cls = 'II'
            else:
                # two-site move on free memory: shared window reads s at address m, t at address m2 != m;
                # s needs a pair blind at both other addresses, t likewise; shared window must be blind
                # for the double change with some value at its third address.
                shapes = []
                for m, m2 in [(0, 1), (0, 2), (1, 2)]:
                    third = 3 - m - m2
                    Ps = B[[k for k in range(3) if k != m][0]] & B[[k for k in range(3) if k != m][1]]
                    Pt = B[[k for k in range(3) if k != m2][0]] & B[[k for k in range(3) if k != m2][1]]
                    found = False
                    for (u, u2) in Ps:
                        for (v, v2) in Pt:
                            for (u, u2) in [(u, u2), (u2, u)]:
                                for z in range(3):
                                    y = [0, 0, 0]; y2 = [0, 0, 0]
                                    y[m], y2[m] = u, u2; y[m2], y2[m2] = v, v2; y[third] = y2[third] = z
                                    if mu(tuple(y)) == mu(tuple(y2)):
                                        found = True
                    if found:
                        shapes.append((m, m2))
                cls = 'I-move%d' % len(shapes) if shapes else ('I-nomove-double%d' % len(double))
            key = (c, cls)
            stats[key] = stats.get(key, 0) + 1
            examples.setdefault(key, (p, q, tp, tq, counts, [sorted(b) for b in B]))
for key in sorted(stats):
    print(key, stats[key], 'example', examples[key])
