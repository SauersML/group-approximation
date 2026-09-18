# Search for an order-3 automorphism alpha of L = F(a,b) with alpha(K) conjugate
# to K, where K = <a, b a b^-2>.  Then G = L x|_alpha Z/3 (which is Z/3 * Z/3
# when alpha is the standard order-3 automorphism) contains g = w s with
# g K g^-1 = K, so [N_G(K) : K] = 3.
import sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from core import red, inv, mul, apply, conj_class

A, B = [1], [2]
K = [A, [2, 1, -2, -2]]
target = conj_class(K)

alpha0 = {1: mul(inv(A), B), 2: inv(A)}   # a -> a^-1 b, b -> a^-1 (from a = t s^2, b = t^2 s)
# check order 3
w = [1, 2, -1, 2, 2]
assert apply(alpha0, apply(alpha0, apply(alpha0, w))) == red(w)

nielsen = [
    {1: [1, 2], 2: [2]}, {1: [2, 1], 2: [2]}, {1: [1], 2: [2, 1]}, {1: [1], 2: [1, 2]},
    {1: [-1], 2: [2]}, {1: [1], 2: [-2]}, {1: [2], 2: [1]},
]


def compose(p, q):  # p after q
    return {1: apply(p, q[1]), 2: apply(p, q[2])}


def inverse_search(beta, depth=12):
    return None


# enumerate beta as words in nielsen moves, together with beta^-1 computed by
# composing inverse moves (inverse of each move listed).
inv_moves = [
    {1: [1, -2], 2: [2]}, {1: [-2, 1], 2: [2]}, {1: [1], 2: [2, -1]}, {1: [1], 2: [-1, 2]},
    {1: [-1], 2: [2]}, {1: [1], 2: [-2]}, {1: [2], 2: [1]},
]
ident = {1: [1], 2: [2]}
frontier = [(ident, ident)]
seen = set()
found = []
for depth in range(6):
    new = []
    for beta, betainv in frontier:
        key = (tuple(beta[1]), tuple(beta[2]))
        if key in seen:
            continue
        seen.add(key)
        for e in (1, 2):
            al = compose(beta, compose(alpha0 if e == 1 else compose(alpha0, alpha0), betainv))
            img = [apply(al, g) for g in K]
            if conj_class(img) == target:
                found.append((depth, al))
        for m, mi in zip(nielsen, inv_moves):
            new.append((compose(beta, m), compose(mi, betainv)))
    frontier = new
    if found:
        break
print("found", len(found))
for d, al in found[:10]:
    print(d, al)
