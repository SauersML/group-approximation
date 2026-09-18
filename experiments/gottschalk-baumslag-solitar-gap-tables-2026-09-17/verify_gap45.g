# Independent check of the 4x5 gap table (GAP 4). Run: gap -q verify_gap45.g < /dev/null
# S = {1, a, t, u} and M = {1, a, t, u, u^2} in BS(2,3) = <a, t | t a^2 t^-1 = a^3>, where u = t^-1 a t.
# Letters: xa, xt, xu for S; ya, yt, yu, yu2 for M.
F := FreeGroup("xa","xt","xu","ya","yt","yu","yu2");;
AssignGeneratorVariables(F);;
# the six forward coincidences s m = s' m' of T_f(S, M)
rels := [ xa/ya,              # (a,1) ~ (1,a)
          xt/yt,              # (t,1) ~ (1,t)
          xu/yu,              # (u,1) ~ (1,u)
          yu2/(xu*yu),        # (1,u^2) ~ (u,u)
          (xa*ya)/(xu*yu2),   # (a,a) ~ (u,u^2): a^2 = u^3
          (xa*yt)/(xt*yu) ];; # (a,t) ~ (t,u)
P := F/rels;;
S := SimplifiedFpGroup(P);;
Print("P(T) simplified: generators ", GeneratorsOfGroup(S), ", relators ", RelatorsOfFpGroup(S), "\n");
F2 := FreeGroup("a","t");;
G := F2/[F2.2*F2.1^2*F2.2^-1*F2.1^-3];;
ga := G.1;; gt := G.2;; gu := gt^-1*ga*gt;;
phi := GroupHomomorphismByImages(P, G, GeneratorsOfGroup(P), [ga, gt, gu, ga, gt, gu, gu^2]);;
Print("label map P(T) -> BS(2,3) is a homomorphism: ", phi <> fail, "\n");
# inverse candidate: a -> xa, t -> xt
psi := GroupHomomorphismByImages(G, P, [ga, gt], [P.1, P.2]);;
Print("a -> x_a, t -> x_t is a homomorphism BS(2,3) -> P(T): ", psi <> fail, "\n");
Print("psi(phi(x_u)) = x_u in P(T): ", Image(psi, Image(phi, P.3)) = P.3, "\n");
# the gap pair: reverse cells (m, s) = (a, u) and (u, a), i.e.  a u  versus  u a
d := (ga*gu)^-1*(gu*ga);;
L := LowIndexSubgroupsFpGroup(G, 8);;
sep := Number(L, H -> not IsOne(d^FactorCosetAction(G, H)));;
Print("transitive representations of degree <= 8: ", Length(L), "; separating the gap pair: ", sep, "\n");
QUIT;
