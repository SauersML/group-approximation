# Edge group of Gamma-bar_9 = Gamma(3,512)/<<[a,c]^2>> under the w13 defect relation.
# In Gamma: (b d) R (b d)^-1 = S . b^320 exactly (hfail-output.txt of w13, e=9), R = [a,c]^2.
# So in Gamma-bar_9: b^320 = S^-1, and u := b^64 = (b^320)^5 = S^-5 =: U lies in the edge group A-bar.
# Conjugation relations of Gamma give, inside A-bar:  U^a = U^3 (from b^a = b^3),
#   c^U = c^(3^64) = c^257 (from c^b = c^3), U^8 = 1 (b^512 = 1).
# Hence A-bar is a quotient of  Etest := < a, c | a^512, c^512, [a,c]^2, U^a = U^3, c^U = c^257, U^8 >.
F := FreeGroup("a", "c");; a := F.1;; c := F.2;;
S := a^341*c^301*a^435*c^299*a^341*c^429*a^435*c^427;;
# same element with exponents reduced to (-256,256] (a^512 = c^512 = 1), to shorten the relators
Sr := a^-171*c^-211*a^-77*c^-213*a^-171*c^-83*a^-77*c^-85;;
U := Sr^-5;;
rels := [a^512, c^512, Comm(a, c)^2, U^-1*a^-1*U*a*U^-2, U^-1*c*U*c^-257, U^8];;
# BOTH = true adds the sigma^2-image (a <-> c, b <-> d): d^64 = U2 := sigma^2(S)^-5 in A-bar,
#   U2^c = U2^3 (from d^c = d^3), a^U2 = a^257 (from a^d = a^3), U2^8 = 1.
if IsBound(BOTH) and BOTH then
  Sr2 := c^-171*a^-211*c^-77*a^-213*c^-171*a^-83*c^-77*a^-85;; U2 := Sr2^-5;;
  Append(rels, [U2^-1*c^-1*U2*c*U2^-2, U2^-1*a*U2*a^-257, U2^8]);
fi;
Etest := F / rels;;
for k in KLIST do
  t := Runtime();
  hom := EpimorphismPGroup(Etest, 2, k);; P := Image(hom);;
  Print("class ", k, " log2 size ", Log(Size(P), 2), " log2 ord(a,c) ",
        List([Etest.1, Etest.2], x -> Log(Order(Image(hom, x)), 2)), " t=", Runtime() - t, "\n");
od;
