# Universal completion of the four distinct pair-cubes in the large
# rank-three K2,2 packet component.

free := FreeGroup("r","y","u","b");;
r:=free.1;; y:=free.2;; u:=free.3;; b:=free.4;;
largeK22 := free/[
  r^3,y^3,u^2,b^2,
  u*r*u*r,
  b*y*b*y,
  (r^-1*b)^3,
  (u*y)^3,
  ((u*r)*y^-1)^3,
  (r*b*y)^3
];;

size := Size(largeK22);;
Print("large_K22_order=",size,"\n");
if size<>infinity then
  gens:=GeneratorsOfGroup(largeK22);;
  Print("first_S3_order=",Order(Group([gens[1],gens[3]])),
        " second_S3_order=",Order(Group([gens[2],gens[4]])),"\n");
  Print("generator_orders=",List(gens,Order),"\n");
  Print("structure=",StructureDescription(largeK22),"\n");
fi;

