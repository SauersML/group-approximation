# Structure of the Nielsen--Soelberg groups G_1, G_2, G_3
# (J. Algebra Appl. 23 (2024) 2550050: (3.1), (3.5), Section 4).
# For each group: the index of the subgroup H named by N--S, whether H is normal,
# a presentation of H on its given generators, a Tietze-simplified presentation,
# and abelian invariants. Core GAP only; package availability is printed first.

for pkg in ["kbmag", "nq", "polycyclic", "ace", "anupq"] do
  Print("package ", pkg, ": ", TestPackageAvailability(pkg), "\n");
od;

ZdsDescribe := function(name, G, Hgens)
  local H, idx, iso, Hf, P, r;
  H := Subgroup(G, Hgens);
  idx := Index(G, H);
  Print("\n== ", name, "\n");
  Print(name, " G^ab = ", AbelianInvariants(G), "\n");
  Print(name, " [G:H] = ", idx, "\n");
  Print(name, " H normal = ", IsNormal(G, H), "\n");
  iso := IsomorphismFpGroupByGenerators(H, Hgens);
  Hf := Range(iso);
  Print(name, " H on given generators: ", Length(RelatorsOfFpGroup(Hf)), " relators\n");
  for r in RelatorsOfFpGroup(Hf) do Print("  ", r, "\n"); od;
  Print(name, " H^ab = ", AbelianInvariants(Hf), "\n");
  P := PresentationFpGroup(Hf);
  TzOptions(P).printLevel := 0;
  TzGoGo(P);
  Print(name, " H after TzGoGo: ", Length(GeneratorsOfPresentation(P)), " generators, ",
        Length(RelatorsOfFpGroup(FpGroupPresentation(P))), " relators\n");
  TzPrintGenerators(P);
  TzPrintRelators(P);
end;

# G_1, (3.1); H from Section 3 (N--S: index 32, normal, presentation (3.2)).
F := FreeGroup("x", "y");; x := F.1;; y := F.2;;
G1 := F / [ y*x^-1*y^-1*x*y^2*x^-1*y^-2*x^-1*y*x*y^-1*x,
            y*x^-1*y*x*y^-1*x^-1*y*x^-1*y*x^-1*y^-1*x ];;
x := G1.1;; y := G1.2;;
ZdsDescribe("G1", G1, [ (x*y)^2, y*x^2*y*x^-1*y^-2*x^-1,
                     x*y^-1*x*y*x*y^-2*x^-1, y^2*x^-1*y*x*y^-1*x^-2 ]);

# G_2, (3.5): generators a1..a8, a_i a_j = a_k a_l for (i,j,k,l) in Y.
F8 := FreeGroup(8);;
Y := [[1,1,2,2],[1,2,3,3],[1,3,4,2],[1,4,3,2],[1,5,3,6],
      [1,7,3,8],[2,1,5,8],[2,3,8,7],[2,4,5,6],[2,5,5,1]];;
G2 := F8 / List(Y, t -> F8.(t[1])*F8.(t[2])*(F8.(t[3])*F8.(t[4]))^-1);;
a := GeneratorsOfGroup(G2);;
ZdsDescribe("G2", G2, [ a[1]^2, a[3]^2, a[6]^2, a[1]*a[3]*a[6]^-1 ]);

# G_3, Section 4.
F := FreeGroup("x", "y");; x := F.1;; y := F.2;;
G3 := F / [ (y*x)^2*(x*y)^2, (x*y^-1)^2*(x*y)^2 ];;
x := G3.1;; y := G3.2;;
ZdsDescribe("G3", G3, [ y^-1*x^-1*y*x, y^2*x^-2, x^-1*y^2*x^-1 ]);

Print("\nGAPDONE\n");
QUIT;
