"""Three-letter absorption certificates for adding c to Delta_0 = <a, c a c^-2>.

c = h3 c^e3 h2 c^e2 h1 c^e1 h0 with h_i in Delta_0; brute force over h0,h1,h2
of length <= L, h3 forced, count solutions whose word is reduced at each c-letter
(no h_i = 1 between opposite letters).
"""
import sys
import itertools
from stallings import subgroup_graph, words, reduce, inv

GENS = ["a", "caCC"]
L = int(sys.argv[1]) if len(sys.argv) > 1 else 5
g0, base = subgroup_graph(GENS)


def member(w):
    return g0.read(base, reduce(w)) == g0.find(base)


elems = [w for w in words(L) if member(w)]
total = 0
for signs in itertools.product("cC", repeat=3):
    e1, e2, e3 = signs
    n = 0
    for h0 in elems:
        for h1 in elems:
            if h1 == "" and e1 == inv(e2):
                continue
            for h2 in elems:
                if h2 == "" and e2 == inv(e3):
                    continue
                h3 = reduce("c" + inv(h0) + inv(e1) + inv(h1) + inv(e2) + inv(h2) + inv(e3))
                if member(h3):
                    n += 1
    total += n
    print(signs, n)
print("total three-letter certificates with |h0|,|h1|,|h2| <=", L, ":", total)
