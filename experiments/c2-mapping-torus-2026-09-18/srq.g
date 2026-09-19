# Certificate that u = x_1^-1 x_0 = y x^-1 y^-1 x is not in H: a transitive permutation
# representation pi: G -> S_n (from a subgroup L of index n) with pi(u) not in pi(H).
F := FreeGroup("x","y");; x := F.1;; y := F.2;;
w := y*x*y^-1*x^-1*x^-1*y*y*x*y^-1*x^-1*y^-1*x*y^-1*y^-1*x*y*x^-1*y;;
G := F / [w];; gG := GeneratorsOfGroup(G);;
hs := [x^-1*y*x*y^-1*x, x^-1*y^3*x, x^-1*y^-1*x*y*x, y, x*y*x^-1];;
u := y*x^-1*y^-1*x;;
NMAX := 9;;
for L in LowIndexSubgroupsFpGroup(G, NMAX) do
  f := FactorCosetAction(G, L);;
  ix := Image(f, gG[1]);; iy := Image(f, gG[2]);;
  P := Group(List(hs, h -> MappedWord(h, [x,y], [ix, iy])));;
  iu := MappedWord(u, [x,y], [ix, iy]);;
  if not iu in P then
    Print("index ", Index(G, L), "  x -> ", ix, "  y -> ", iy, "  |pi(G)| = ", Size(Image(f)),
          "  |pi(H)| = ", Size(P), "\n");
    break;
  fi;
od;
QUIT;
