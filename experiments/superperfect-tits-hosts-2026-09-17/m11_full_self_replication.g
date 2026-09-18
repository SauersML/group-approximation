# Instance check for tits-hosts-for-transitive-local-actions, item 6.
# F = M_12 on C = {1..12}; F_0 = Stab(12) = M_11 acting on X = {1..11}; the root letter "0" is point 1.
# b = (b, alpha, beta, 1, ..., 1): section b at 1, alpha at 2, beta at 3, trivial elsewhere, trivial root permutation.
# For a in P_1 = Stab_{M_11}(1), h_a = b^-1 a b a^-1 has section 1 at 1 and s_x(b)^-1 s_{a^-1 x}(b) in M_11 at x = 2..11.
# The script builds H = <h_a> <= M_11^10 (coordinates 2..11) and checks every pair projection is onto M_11 x M_11.
M12 := MathieuGroup(12);
P := Stabilizer(M12, 12);
Print("|P| = ", Size(P), "  moved points = ", MovedPoints(P), "  transitive on 1..11: ", IsTransitive(P, [1..11]), "\n");
Print("P perfect: ", IsPerfectGroup(P), "  H_2(P) = ", AbelianInvariantsMultiplier(P), "\n");
Print("M_12 = <point stabilizers>: ", Size(Group(Union(List([1..12], c -> GeneratorsOfGroup(Stabilizer(M12, c)))))) = Size(M12), "\n");
P1 := Stabilizer(P, 1);
alpha := (1,2,3,4,5,6,7,8,9,10,11);;
if not alpha in P then alpha := First(Elements(P), g -> Order(g) = 11); fi;
beta := First(Elements(P), g -> Order(g) = 5 and 1^g <> 1);;
Print("alpha = ", alpha, "  beta = ", beta, "\n");
sec := function(x)   # section of b at letter x (x = 2..11); x = 1 not used
  if x = 2 then return alpha; elif x = 3 then return beta; else return (); fi;
end;
D := DirectProduct(List([2..11], i -> P));
emb := List([1..10], i -> Embedding(D, i));
proj := List([1..10], i -> Projection(D, i));
# Convention: GAP permutations act on the right, and so do the tree automorphisms: (x w)^s = x^(pi_s) w^(s|_x).
# Then (st)|_x = s|_x * t|_(x^pi_s), and h_a = b^-1 a b a^-1 has section s_x^-1 * s_(x^a) at x.
# As a runs over P_1 so does a^-1, so the generators below are the h_(a^-1).
hgen := function(a)
  return Product([1..10], i -> Image(emb[i], sec(i+1)^-1 * sec((i+1)^Inverse(a))));
end;

gens := List(GeneratorsOfGroup(P1), hgen);
Append(gens, List([1..20], k -> hgen(PseudoRandom(P1))));
H := Group(gens);
Print("|H| = ", Size(H), "  |M_11|^10 = ", Size(P)^10, "\n");
ok := true;
for i in [1..10] do for j in [i+1..10] do
  pr := Group(List(gens, g -> Image(emb[1], Image(proj[i], g)) * Image(emb[2], Image(proj[j], g))));
  if Size(pr) <> Size(P)^2 then ok := false; Print("pair ", i+1, ",", j+1, " order ", Size(pr), "\n"); fi;
od; od;
Print("all 45 pair projections onto M_11 x M_11: ", ok, "\n");
# (PSL(2,8) has trivial Schur multiplier (ATLAS); not checked here: this GAP lacks the SmallGroups library needed by the multiplier routine for it.)
QUIT;
