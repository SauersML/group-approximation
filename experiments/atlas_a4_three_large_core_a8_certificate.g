# Exact A8 permutation certificate satisfying the minimal forward-collision
# presentation and three of the four distinct large-component core edges.

r := PermList([1,2,5,3,4,7,8,6]);;
z := PermList([1,2,4,5,3,7,8,6]);;
c := PermList([2,1,6,8,7,3,5,4]);;
t := PermList([2,4,7,1,3,6,5,8]);;
s := PermList([3,5,1,7,2,8,4,6]);;
u := PermList([2,1,7,8,6,5,3,4]);;
b := s*t;;
y := t^-1;;
q := t*c*s*c*t^-1*c*s*t*c;;

minimalRels := [
  r^3,z^3,Comm(z,r),c^2,Comm(c,r),c*z*c*z,
  t^3,s^2,(s*t)^2,(r^-1*b)^3,(z*b)^3,q,
  u^2,(u*r)^2,Comm(u,z),Comm(u,c)
];;
largeChecks := [
  IsOne((r^-1*b)^3),
  IsOne((u*y)^3),
  IsOne(((u*r)*y^-1)^3),
  IsOne((r*b*y)^3)
];;

Q:=Group([r,z,c,t,s,u]);;
C:=Group([r,z,b]);;
F:=Group([r,z,c]);;
K:=Group([t,s]);;
H:=Group([r,z,c,u]);;
E1:=Group([r^-1,b]);;
E2:=Group([u,y]);;
E3:=Group([u*r,y^-1]);;

if not ForAll(minimalRels,IsOne) then Error("minimal relator failed"); fi;
if largeChecks<>[true,true,true,false] then Error("large-core mask changed"); fi;
if [Order(C),Order(F),Order(K),Order(H)]<>[144,18,6,36] then
  Error("vertex order changed");
fi;
if [Order(E1),Order(E2),Order(E3)]<>[12,12,12] then
  Error("A4 edge failed to inject");
fi;
if Order(Q)<>20160 or not ForAll([r,z,c,t,s,u],x->SignPerm(x)=1) then
  Error("image is not A8");
fi;

Print("{\n");
Print("  \"all_minimal_relators_identity\": true,\n");
Print("  \"large_core_checks\": [true,true,true,false],\n");
Print("  \"missing_fourth_word_order\": ",Order(r*b*y),",\n");
Print("  \"image_is_A8\": true,\n");
Print("  \"image_order\": ",Order(Q),",\n");
Print("  \"vertex_orders\": {\"C\":144,\"F\":18,\"H\":36,\"K\":6}\n");
Print("}\n");

