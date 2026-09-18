# Lower bound H_2(A_5 wr A_5) ->> (Z/2)^2 by an explicit perfect central extension.
# S = SL(2,5), a perfect central extension of A_5 by Z/2, acting on 5 points through A_5
# (conjugation on its 5 Sylow 2-subgroups).
# Ew = S wr_5 S, built as the fibre product of (S wr_5 A_5) -> A_5 <- S, since GAP's WreathProduct
# uses the image A_5 of the action as top group.
# K = Z(S)^5 x Z(S) is the kernel of Ew -> A_5 wr A_5, and Z0 = even-weight part of Z(S)^5.
# If Ew is perfect, |Ew/K| = 60^6 and [Ew,K] <= Z0, then Ew/Z0 is a perfect central extension of
# A_5 wr A_5 with kernel K/Z0 = (Z/2)^2, so the Schur multiplier of A_5 wr A_5 maps onto (Z/2)^2.
# (No quotient group is formed: GAP's quotient routine needs the transgrp package here.)
G0 := SL(2,5);
S := Image(IsomorphismPermGroup(G0), G0);
Print("S: order ", Size(S), ", ", StructureDescription(S), "\n");
syl := ConjugacyClassSubgroups(S, SylowSubgroup(S, 2));
act := ActionHomomorphism(S, AsList(syl), OnPoints);
A := Image(act);
Print("action image: size ", Size(A), " on ", NrMovedPoints(A), " points\n");
W := WreathProduct(S, A);
emb := List([1..6], i -> Embedding(W, i));
D := DirectProduct(W, S);
d1 := Embedding(D, 1);; d2 := Embedding(D, 2);;
base := Concatenation(List([1..5], i -> List(GeneratorsOfGroup(S), s -> Image(d1, Image(emb[i], s)))));
top := List(GeneratorsOfGroup(S), t -> Image(d1, Image(emb[6], Image(act, t))) * Image(d2, t));
Ew := Subgroup(D, Concatenation(base, top));
Print("|E| = ", Size(Ew), "  = 120^6: ", Size(Ew) = 120^6, "  perfect: ", IsPerfectGroup(Ew), "\n");
z := First(Elements(Centre(S)), x -> x <> One(S));
zs := List([1..5], i -> Image(d1, Image(emb[i], z)));
ztop := Image(d2, z);
K := Subgroup(Ew, Concatenation(zs, [ztop]));
Z0 := Subgroup(Ew, List([1..4], i -> zs[i] * zs[i+1]));
Print("|K| = ", Size(K), "  |Z0| = ", Size(Z0), "  |E/K| = 60^6: ", Size(Ew)/Size(K) = 60^6,
      "  K normal: ", IsNormal(Ew, K), "  Z0 normal: ", IsNormal(Ew, Z0), "\n");
C := CommutatorSubgroup(Ew, K);
Print("K invariants: ", AbelianInvariants(K), "  [Ew,K] = Z0: ", C = Z0,
      "  so K/Z0 is central in Ew/Z0, elementary abelian of order ", Size(K)/Size(Z0), "\n");
QUIT;
