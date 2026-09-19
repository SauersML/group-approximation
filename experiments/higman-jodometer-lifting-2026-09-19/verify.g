# Independent GAP check of a jlift model (file MODEL, set before reading): relators of H4(3) and [a,c]^2, the j-odometer shape of a,
# tree-automorphism property, orders, and the group it generates.
Read(MODEL);
a := model[1]; b := model[2]; c := model[3]; d := model[4];
rels := [ b^a / b^3, c^b / c^3, d^c / d^3, a^d / a^3, Comm(a, c)^2 ];
Print("relators trivial: ", ForAll(rels, IsOne), "\n");
Print("orders (a,b,c,d): ", List(model, Order), "\n");
# tree property on Z/2^k (point x+1 <-> residue x): x = y mod 2^m  =>  images agree mod 2^m
deg := 2^LogInt(Maximum(List(model, g -> LargestMovedPoint(g))), 2);
if deg < Maximum(List(model, g -> LargestMovedPoint(g))) then deg := 2 * deg; fi;
tree := ForAll(model, g -> ForAll([0 .. LogInt(deg, 2)], m ->
          ForAll([0 .. deg - 1], x -> ((x + 2^m) mod deg = x) or
             ((((x + 1)^g - 1) - ((((x + 2^m) mod deg) + 1)^g - 1)) mod 2^m = 0))));
Print("degree ", deg, ", tree automorphisms: ", tree, "\n");
Print("a-orbit lengths: ", Collected(List(Orbits(Group(a), [1 .. deg]), Length)), "\n");
G := Group(model);
Print("|G| = 2^", LogInt(Size(G), 2), ", is 2-group: ", IsPGroup(G), ", transitive: ", IsTransitive(G, [1 .. deg]), "\n");
QUIT;
