import itertools
from census2 import classify, Y
# For class II rules: blind-pair count per coordinate, and the diagonal split.
shapes = {}
for c in [(1, 1, 2), (1, 1, 0)]:
    for p, q in itertools.combinations(Y, 2):
        if not set(p) & set(q):
            continue
        for tp, tq in itertools.product((1, 2), repeat=2):
            counts, diag_inj, rigid, cls, B = classify(c, p, q, tp, tq)
            if counts == [9, 9, 9] or not rigid or cls != 'II':
                continue
            key = (tuple(len(b) for b in B), diag_inj, len({tuple(x) for b in B for x in b}))
            shapes[key] = shapes.get(key, 0) + 1
print(shapes)
