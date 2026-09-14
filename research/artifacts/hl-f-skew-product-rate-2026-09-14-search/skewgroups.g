# Order, solvability, derived length and structure of the skew-product certificates below ratio 1/3.
certs := [
  ["4/21 torus3 x Sym3 fibre, n=27", [9,10,11,12,13,14,16,17,15,20,19,18,21,22,23,25,26,24,0,1,2,4,3,5,7,8,6], [5,3,4,7,8,6,0,1,2,14,13,12,17,16,15,11,10,9,23,21,22,25,26,24,18,19,20]],
  ["3/11 torus3 x Sym4 fibre, n=36", [15,13,12,14,18,19,17,16,20,22,21,23,24,25,27,26,29,30,28,31,32,35,34,33,3,1,2,0,5,7,4,6,8,11,9,10], [4,5,7,6,8,9,11,10,0,1,2,3,17,18,16,19,20,22,21,23,14,13,12,15,28,30,29,31,33,34,32,35,25,24,26,27]]
];
for c in certs do
  A := PermList(List(c[2], x -> x+1));; B := PermList(List(c[3], x -> x+1));;
  G := Group(A, B);; sol := IsSolvableGroup(G);;
  if sol then dl := DerivedLength(G); else dl := -1; fi;
  Print(c[1], " | order ", Size(G), " | solvable ", sol, " | derived length ", dl, " | structure ", StructureDescription(G), "\n");
od;
QUIT;
