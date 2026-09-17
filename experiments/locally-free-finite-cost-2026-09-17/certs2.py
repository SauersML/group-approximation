"""Two-letter absorption certificates for adding c to Delta_0 = <a, c a c^-2> in F(a,c).

A certificate is (h0, h1, h2) in Delta_0^3 with  c = h2 c^e h1 c^d h0.
Brute force: enumerate h1, h0 in Delta_0 up to length L (as reduced words that
are closed paths at the base of the Stallings graph), put
h2 = c h0^-1 c^-d h1^-1 c^-e and test h2 in Delta_0.
Malnormality of Delta_0 makes h2, h0 unique given h1.
"""
import sys
from stallings import subgroup_graph, words, reduce, inv

GENS = ["a", "caCC"]
L = int(sys.argv[1]) if len(sys.argv) > 1 else 6
g0, base = subgroup_graph(GENS)


def member(w):
    return g0.read(base, reduce(w)) == g0.find(base)


elems = [w for w in words(L) if member(w)]
print("elements of Delta_0 of length <=", L, ":", len(elems))
for e, d in [("c", "c"), ("c", "C"), ("C", "c"), ("C", "C")]:
    sols = []
    for h1 in elems:
        for h0 in elems:
            h2 = reduce("c" + inv(h0) + inv(d) + inv(h1) + inv(e))
            if member(h2) and reduce(h2 + e + h1 + d + h0) == "c":
                sols.append((h0, h1, h2))
    print(e, d, "solutions:", len(sols))
    for s in sols[:15]:
        print("   h0=%-10s h1=%-10s h2=%s" % s)
