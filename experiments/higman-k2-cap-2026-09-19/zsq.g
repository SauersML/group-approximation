# zsq.g: for each I, is z = a^(ord(a)/2) in gamma_I(P)^2 ?  (SS[I] = log2 |P_(I-1)|)
Read(PQF); pcgs := Pcgs(F);; n := Length(pcgs);; one := One(GF(2));;
gi := List([1..4], i -> MapImages[i]);; z := gi[1]^(Order(gi[1])/2);;
ex := g -> ExponentsOfPcElement(pcgs, g);;
Print("weight of a^(2^j): ", List([0..7], j -> PositionNonZero(ex(gi[1]^(2^j)))), "\n");
for I in [8..14] do
  Aidx := [SS[I]+1..n];
  R := List(Aidx, t -> ex(pcgs[t]^2){Aidx} * one);
  Print("I = ", I, " dim A = ", Length(Aidx), " dim A/A^2 = ", Length(Aidx) - RankMat(R),
    " z in A^2: ", SolutionMat(R, ex(z){Aidx} * one) <> fail, "\n");
od;
QUIT;
