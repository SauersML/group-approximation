# Order, solvability and derived length of the landed hl-f-sofic-relator-instability certificate pairs.
certs := [
  ["cert.s10 (sum ratio 1/2, n=10)", [1,2,3,4,0,6,7,8,9,5], [3,4,5,1,7,8,9,0,6,2]],
  ["cert.x12 (max ratio 1/3, n=12)", [1,2,3,0,5,6,7,4,9,8,11,10], [4,5,8,9,1,0,10,2,3,11,7,6]],
  ["cert.x16 (max ratio 4/13, n=16)", [0,4,6,8,9,1,12,2,13,11,7,5,14,3,10,15], [0,5,7,2,11,9,13,3,6,1,14,15,10,8,12,4]],
  ["cert.10 (4/10)", [3,6,9,2,4,1,5,0,8,7], [9,1,0,4,7,8,5,3,6,2]],
  ["cert.12 (4/11)", [8,0,7,9,6,10,4,1,11,5,3,2], [9,5,3,8,1,4,10,6,2,11,7,0]]
];
for c in certs do
  A := PermList(List(c[2], x -> x+1));; B := PermList(List(c[3], x -> x+1));;
  G := Group(A, B);;
  sol := IsSolvableGroup(G);;
  if sol then dl := DerivedLength(G); else dl := "not solvable"; fi;
  Print(c[1], " | order ", Size(G), " | solvable ", sol, " | derived length ", dl,
        " | metabelian ", IsSolvableGroup(G) and DerivedLength(G) <= 2,
        " | structure ", StructureDescription(G), "\n");
od;
QUIT;
