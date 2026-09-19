# e = 10 analogue of abartest.g (BOTH): in Gamma(3,1024), (b d) R (b d)^-1 = S . b^832 exactly
# (hfail-output.txt of w13, e = 10), R = [a,c]^2. In Gammabar_10: b^832 = S^-1, so
# U := S^-5 = b^4160 = b^64 lies in the edge image; U^a = U^3, c^U = c^(3^64) = c^257 (mod 1024),
# U^16 = 1. sigma^2 gives V := sigma^2(S)^-5 = d^64 with V^c = V^3, a^V = a^257, V^16 = 1.
F := FreeGroup("a", "c");; a := F.1;; c := F.2;;
S := a^341*c^301*a^435*c^299*a^341*c^429*a^435*c^939;;
S2 := c^341*a^301*c^435*a^299*c^341*a^429*c^435*a^939;;
U := S^-5;; V := S2^-5;;
rels := [a^1024, c^1024, Comm(a, c)^2, U^-1*a^-1*U*a*U^-2, U^-1*c*U*c^-257, U^16,
         V^-1*c^-1*V*c*V^-2, V^-1*a*V*a^-257, V^16];;
Etest := F / rels;;
for k in KLIST do
  t := Runtime();
  hom := EpimorphismPGroup(Etest, 2, k);; P := Image(hom);;
  Print("class ", k, " log2 size ", Log(Size(P), 2), " log2 ord(a,c) ",
        List([Etest.1, Etest.2], x -> Log(Order(Image(hom, x)), 2)), " t=", Runtime() - t, "\n");
od;
QUIT;
