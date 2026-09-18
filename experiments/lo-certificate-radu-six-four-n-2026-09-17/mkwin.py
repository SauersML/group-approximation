"""Window presentation W(h,t) that surjects onto Gamma_{6,4n} for every n >= max(h/2, (t+3)/2, 2)
Generators a1,a2,a3,b3 (b2 = a3 b3 a3^-1, b1 = a3 b2 a3^-1, z = b_{2n} = a3 b1 a3^-1).
Head: b_4..b_h from b_3 (b_{2j} = a1^-1 b_{2j-1} a1^-1, b_{2j+1} = a2^-1 b_{2j} a2^-1) with the J/K relators.
Tail: y_0 = z, y_1 = b_{2n-1} = a1 z a1, y_2 = b_{2n-2} = a2 y_1 a2, ... down to y_t, with the J/K relators.
Also: Reidemeister-Schreier on the index-4 kernel of W/ncl([a1^3,a2^4]) (perfectness check).
usage: python3 mkwin.py h t MAX > file.g"""
import sys
h, t, mx = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
s = 'F := FreeGroup("a1","a2","a3","b3");;\na1:=F.1;; a2:=F.2;; a3:=F.3;; b3:=F.4;;\n'
s += "b2 := a3*b3*a3^-1;;\nb1 := a3*b2*a3^-1;;\nz := a3*b1*a3^-1;;\n"
rels = ["a1*b1*a2^-1*b1", "a1*b2*a2*b2^-1", "a1*b2^-1*a2^-1*b1^-1", "a1*b1^-1*a2^-1*b2",
        "a2*b3*a2^-1*b3", "a2*z*a2^-1*z"]
for k in range(4, h + 1):
    x = "a1" if k % 2 == 0 else "a2"
    s += "b%d := %s^-1*b%d*%s^-1;;\n" % (k, x, k - 1, x)
    rels += ["%s^-1*b%d*a3^-1*b%d^-1" % (x, k, k - 1), "a3*b%d*%s^-1*b%d^-1" % (k, x, k - 1)]
s += "y0 := z;;\n"
for i in range(1, t + 1):
    x = "a1" if i % 2 == 1 else "a2"   # b_{2n-i} = x y_{i-1} x ; b_{2n-i+1} = y_{i-1} is even-indexed iff i odd
    s += "y%d := %s*y%d*%s;;\n" % (i, x, i - 1, x)
    rels += ["%s^-1*y%d*a3^-1*y%d^-1" % (x, i - 1, i), "a3*y%d*%s^-1*y%d^-1" % (i - 1, x, i)]
s += "rels := [%s];;\n" % ", ".join(rels)
s += "ex := [Comm(a1^3, a2^4), Comm(a2^3, a1^4)];;\n"
s += 'Print("W(%d,%d) nrels=", Length(rels), " ab=", AbelianInvariants(F/rels), "\\n");\n' % (h, t)
s += "tt := Runtime();;\n"
s += "ct := CosetTableFromGensAndRels(GeneratorsOfGroup(F), Concatenation(rels, ex), [a1] : max := %d, silent := true);;\n" % mx
s += 'if ct = fail then Print("W(%d,%d) H=[a1] FAIL ", Runtime()-tt, "ms\\n");\n' % (h, t)
s += 'else Print("W(%d,%d) H=[a1] index ", Length(ct[1]), " ", Runtime()-tt, "ms\\n"); fi;\n' % (h, t)
s += "Q := F / Concatenation(rels, [Comm(a1^3, a2^4)]);;\n"
s += "if AbelianInvariants(Q) = [2,2] then K := Kernel(MaximalAbelianQuotient(Q));\n"
s += '  Print("W(%d,%d) [Q:Q\'] = ", Index(Q, K), " abelian invariants of Q\': ", AbelianInvariants(Image(IsomorphismFpGroup(K))), "\\n");\n' % (h, t)
s += 'else Print("W(%d,%d) Q^ab = ", AbelianInvariants(Q), "\\n"); fi;\nQUIT;\n' % (h, t)
print(s)
