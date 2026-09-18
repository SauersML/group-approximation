"""GAP script: abelian invariants of Q' for Q = Gamma_{6,4n}/ncl([a1^3,a2^4]) (squares from fig64n.py).
Q' has index 4 in Q (Q^ab = C2^2), so Reidemeister-Schreier is cheap.  Output [] means Q' is perfect.
usage: python3 mkperf.py n > file.g ; gap -q file.g < /dev/null"""
import sys
import fig64n
from bmw import BMW, parse_word


def gapword(w):
    return "*".join("%s%d%s" % (t, abs(x), "^-1" if x < 0 else "") for t, x in parse_word(w))


n = int(sys.argv[1])
sq = fig64n.instantiate(fig64n.build(n), n)
rels = [fig64n.fmtw(fig64n.word(s, 0)) for _, _, s in sq]
BMW(3, 2 * n, rels)
gens = ["a1", "a2", "a3"] + ["b%d" % j for j in range(1, 2 * n + 1)]
s = 'F := FreeGroup(%s);\n' % ",".join('"%s"' % g for g in gens)
s += "".join("%s := F.%d;\n" % (g, i + 1) for i, g in enumerate(gens))
s += "rels := [%s];\n" % ", ".join(gapword(r) for r in rels)
s += "Q := F / Concatenation(rels, [Comm(a1^3, a2^4)]);\n"
s += 'Print("n=%d Q^ab=", AbelianInvariants(Q), "\\n");\n' % n
s += "hom := MaximalAbelianQuotient(Q);\nK := Kernel(hom);\n"
s += 'Print("n=%d [Q:Q\'] = ", Index(Q, K), "\\n");\n' % n
s += "P := Image(IsomorphismFpGroup(K));\n"
s += 'Print("n=%d abelian invariants of Q\': ", AbelianInvariants(P), "\\n");\nQUIT;\n' % n
print(s)
