# Independent check of the 3x6 and 4x5 gap tables (GAP 4). Run: gap -q verify_gap36.g < /dev/null
F2 := FreeGroup("a","t");;
G := F2/[F2.2*F2.1^2*F2.2^-1*F2.1^-3];;
ga := G.1;; gt := G.2;;
L := LowIndexSubgroupsFpGroup(G, 8);;
Print("transitive representations of BS(2,3) of degree <= 8: ", Length(L), "\n");

# ---- 3x6: S = {1, t, t a}, M = {1, a, a^-1, a^-2, a^-1 t^-1 a, a^-2 t^-1 a}
F := FreeGroup("xt","xta","ya","yA","yAA","yATa","yAATa");;
AssignGeneratorVariables(F);;
rels := [ ya/(xta*yATa),          # (1,a)     ~ (ta, a^-1 t^-1 a)
          (xt*ya)/xta,            # (t,a)     ~ (ta,1)
          xt/(xta*yA),            # (t,1)     ~ (ta,a^-1)
          (xt*yA)/(xta*yAA),      # (t,a^-1)  ~ (ta,a^-2)
          (xt*yATa)/(xta*yAATa),  # (t,a^-1 t^-1 a) ~ (ta, a^-2 t^-1 a)
          yAA/(xt*yAATa) ];;      # (1,a^-2)  ~ (t, a^-2 t^-1 a)
P := F/rels;;
S := SimplifiedFpGroup(P);;
Print("3x6: P(T) simplified: generators ", GeneratorsOfGroup(S), ", relators ", RelatorsOfFpGroup(S), "\n");
imgs := [gt, gt*ga, ga, ga^-1, ga^-2, ga^-1*gt^-1*ga, ga^-2*gt^-1*ga];;
Print("3x6: label map P(T) -> BS(2,3) is a homomorphism: ",
      ForAll(rels, r -> MappedWord(r, GeneratorsOfGroup(F), imgs) = One(G)), "\n");
# gap pair: reverse cells (a^-1 t^-1 a, t) and (a^-2 t^-1 a, t a)
d := (ga^-1*gt^-1*ga*gt)^-1*(ga^-2*gt^-1*ga*gt*ga);;
Print("3x6: gap pair distinct in BS(2,3) (a and t^-1 a t do not commute): ",
      not IsOne(Comm(ga, gt^-1*ga*gt)) , "\n");
Print("3x6: transitive representations of degree <= 8 separating the gap pair: ",
      Number(L, H -> not IsOne(d^FactorCosetAction(G, H))), "\n");

# ---- 4x5: S = {1, a, t, u}, M = {1, a, t, u, u^2}, u = t^-1 a t
F := FreeGroup("xa","xt","xu","ya","yt","yu","yu2");;
AssignGeneratorVariables(F);;
rels := [ xa/ya, xt/yt, xu/yu, yu2/(xu*yu), (xa*ya)/(xu*yu2), (xa*yt)/(xt*yu) ];;
P := F/rels;;
S := SimplifiedFpGroup(P);;
Print("4x5: P(T) simplified: generators ", GeneratorsOfGroup(S), ", relators ", RelatorsOfFpGroup(S), "\n");
gu := gt^-1*ga*gt;;
imgs := [ga, gt, gu, ga, gt, gu, gu^2];;
Print("4x5: label map P(T) -> BS(2,3) is a homomorphism: ",
      ForAll(rels, r -> MappedWord(r, GeneratorsOfGroup(F), imgs) = One(G)), "\n");
d := (ga*gu)^-1*(gu*ga);;
Print("4x5: transitive representations of degree <= 8 separating the gap pair a*u, u*a: ",
      Number(L, H -> not IsOne(d^FactorCosetAction(G, H))), "\n");
QUIT;
