# Independent check of the 5x5 gap table (GAP 4). Run: gap -q verify_gap55.g < /dev/null
# Letters: x_a, x_t, x_a3, x_s5 for S = {1, a, t, a^3, s5 = t^-1 a t a^-1};
#          y_a, y_a2, y_t, y_m5 for M = {1, a, a^2, t, m5 = t^-1 a t}.
F := FreeGroup("xa","xt","xa3","xs5","ya","ya2","yt","ym5");;
AssignGeneratorVariables(F);;
# the seven forward coincidences s m = s' m' of T_f(S, M) in BS(2,3)
rels := [ xa/ya,                 # (a,1)    ~ (1,a)
          ya2/(xa*ya),           # (1,a^2)  ~ (a,a)
          xt/yt,                 # (t,1)    ~ (1,t)
          ym5/(xs5*ya),          # (1,m5)   ~ (s5,a)
          (xa*ya2)/xa3,          # (a,a^2)  ~ (a^3,1)
          (xa*yt)/(xt*ym5),      # (a,t)    ~ (t,m5)
          (xt*ya2)/(xa3*yt) ];;  # (t,a^2)  ~ (a^3,t)
P := F/rels;;
S := SimplifiedFpGroup(P);;
Print("P(T) simplified: generators ", GeneratorsOfGroup(S), ", relators ", RelatorsOfFpGroup(S), "\n");
F2 := FreeGroup("a","t");;
G := F2/[F2.2*F2.1^2*F2.2^-1*F2.1^-3];;
ga := G.1;; gt := G.2;;
imgs := [ga, gt, ga^3, gt^-1*ga*gt*ga^-1, ga, ga^2, gt, gt^-1*ga*gt];;
Print("label map P(T) -> BS(2,3) is a homomorphism: ",
      ForAll(rels, r -> MappedWord(r, GeneratorsOfGroup(F), imgs) = One(G)), "\n");
# the gap pair y_a x_s5 versus y_m5 is  a t^-1 a t a^-1  versus  t^-1 a t
d := (ga*gt^-1*ga*gt*ga^-1)^-1*(gt^-1*ga*gt);;
L := LowIndexSubgroupsFpGroup(G, 8);;
sep := Number(L, H -> not IsOne(d^FactorCosetAction(G, H)));;
Print("transitive representations of degree <= 8: ", Length(L), "; separating the gap pair: ", sep, "\n");
QUIT;
