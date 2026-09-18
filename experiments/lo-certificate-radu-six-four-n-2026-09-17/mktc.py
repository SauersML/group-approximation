"""GAP script for Radu's Gamma_{6,4n} (squares read from Figure picture:64n by fig64n.py):
Gamma^ab, Q^ab and Todd-Coxeter enumerations of Q = Gamma/ncl([a1^3,a2^4]) over <a1> and over
the trivial subgroup.  An enumeration that closes gives the exact index.
usage: python3 mktc.py n > file.g ; gap -q file.g < /dev/null"""
import sys
import fig64n
from bmw import BMW, parse_word


def gapword(w):
    return "*".join("%s%d%s" % (t, abs(x), "^-1" if x < 0 else "") for t, x in parse_word(w))


n = int(sys.argv[1])
sq = fig64n.instantiate(fig64n.build(n), n)
rels = [fig64n.fmtw(fig64n.word(s, 0)) for _, _, s in sq]
BMW(3, 2 * n, rels)  # asserts a complete VH datum
gens = ["a1", "a2", "a3"] + ["b%d" % j for j in range(1, 2 * n + 1)]
s = 'F := FreeGroup(%s);\n' % ",".join('"%s"' % g for g in gens)
s += "".join("%s := F.%d;\n" % (g, i + 1) for i, g in enumerate(gens))
s += "rels := [%s];\n" % ", ".join(gapword(r) for r in rels)
s += 'Print("n=%d squares=", Length(rels), " Gamma^ab=", AbelianInvariants(F / rels), "\\n");\n' % n
s += "Q := F / Concatenation(rels, [Comm(a1^3, a2^4)]);\n"
s += 'Print("n=%d Q^ab=", AbelianInvariants(Q), "\\n");\n' % n
s += "for H in [[a1], []] do\n  t := Runtime();\n"
s += "  ct := CosetTableFromGensAndRels(GeneratorsOfGroup(F), RelatorsOfFpGroup(Q), H : max := 4000000, silent := true);\n"
s += '  if ct = fail then Print("n=%d H=", H, " FAIL ", Runtime()-t, "ms\\n");\n' % n
s += '  else Print("n=%d H=", H, " index ", Length(ct[1]), " ", Runtime()-t, "ms\\n"); fi;\nod;\nQUIT;\n' % n
print(s)
