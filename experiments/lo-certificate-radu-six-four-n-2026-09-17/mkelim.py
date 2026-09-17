"""GAP script: Gamma_{6,4n}/ncl(c[,d]) on the 4 generators a1,a2,a3,b3 after Tietze elimination
b2 = a3 b3 a3^-1, b1 = a3 b2 a3^-1, b_{2j} = a1^-1 b_{2j-1} a1^-1, b_{2j+1} = a2^-1 b_{2j} a2^-1
(the relators used for elimination are kept, harmlessly, as trivial relators).
Enumerates cosets of <a1>, then computes the abelian invariants of Q' for Q = Gamma/ncl(c) (perf).
usage: python3 mkelim.py n MAX [cd] > file.g   (n = 0: uniform group D, enumeration only)"""
import sys
import fig64n
from bmw import BMW, parse_word

n, mx = int(sys.argv[1]), int(sys.argv[2])
cd = len(sys.argv) > 3
s = 'F := FreeGroup("a1","a2","a3","b3");;\na1:=F.1;; a2:=F.2;; a3:=F.3;; b3:=F.4;;\n'
s += "b2 := a3*b3*a3^-1;;\nb1 := a3*b2*a3^-1;;\n"
if n > 0:
    for k in range(4, 2 * n + 1):
        s += "b%d := %s*b%d*%s;;\n" % (k, "a1^-1" if k % 2 == 0 else "a2^-1", k - 1, "a1^-1" if k % 2 == 0 else "a2^-1")
    sq = fig64n.instantiate(fig64n.build(n), n)
    rels = [fig64n.fmtw(fig64n.word(q, 0)) for _, _, q in sq]
    BMW(3, 2 * n, rels)
    g = lambda w: "*".join("%s%d%s" % (t, abs(x), "^-1" if x < 0 else "") for t, x in parse_word(w))
    s += "rels := [%s];;\n" % ", ".join(g(r) for r in rels)
else:
    s += "z := a3*b1*a3^-1;;\nb4 := a1^-1*b3*a1^-1;;\nbl := a1*z*a1;;\n"
    s += ("rels := [a1*b1*a2^-1*b1, a1*b2*a2*b2^-1, a1*b2^-1*a2^-1*b1^-1, a1*b1^-1*a2^-1*b2, "
          "a2*b3*a2^-1*b3, a2*z*a2^-1*z, a1^-1*b4*a3^-1*b3^-1, a3*b4*a1^-1*b3^-1, "
          "a1^-1*z*a3^-1*bl^-1, a3*z*a1^-1*bl^-1];;\n")
s += "rels := Filtered(rels, r -> Length(r) > 0);;\n"
s += "ex := [Comm(a1^3, a2^4)%s];;\n" % (", Comm(a2^3, a1^4)" if cd else "")
s += 'Print("n=%d cd=%s nrels=", Length(rels), " ab=", AbelianInvariants(F/rels), "\\n");\n' % (n, cd)
s += "t := Runtime();;\n"
s += "ct := CosetTableFromGensAndRels(GeneratorsOfGroup(F), Concatenation(rels, ex), [a1] : max := %d, silent := true);;\n" % mx
s += 'if ct = fail then Print("n=%d cd=%s H=[a1] FAIL ", Runtime()-t, "ms\\n");\n' % (n, cd)
s += 'else Print("n=%d cd=%s H=[a1] index ", Length(ct[1]), " ", Runtime()-t, "ms\\n"); fi;\n' % (n, cd)
if n > 0:
    s += "Q := F / Concatenation(rels, [Comm(a1^3, a2^4)]);;\nK := Kernel(MaximalAbelianQuotient(Q));;\n"
    s += 'Print("n=%d [Q:Q\'] = ", Index(Q, K), " abelian invariants of Q\': ", AbelianInvariants(Image(IsomorphismFpGroup(K))), "\\n");\n' % n
s += "QUIT;\n"
print(s)
