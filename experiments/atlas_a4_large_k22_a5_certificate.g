# Exact faithful A5 completion of the full large rank-three K2,2 component.

r := PermList([1,2,4,5,3]);;
y := PermList([2,3,1,4,5]);;
u := PermList([2,1,4,3,5]);;
b := PermList([3,2,1,5,4]);;

rels := [
  r^3,y^3,u^2,b^2,
  u*r*u*r,b*y*b*y,
  (r^-1*b)^3,(u*y)^3,((u*r)*y^-1)^3,(r*b*y)^3
];;
vertices := [Group([r,u]),Group([y,b])];;
edges := [Group([r^-1,b]),Group([u,y]),
          Group([u*r,y^-1]),Group([r,b*y])];;
Q := Group([r,y,u,b]);;

if not ForAll(rels,IsOne) then Error("large K2,2 relation failed"); fi;
if List(vertices,Order)<>[6,6] then Error("S3 vertex collapsed"); fi;
if List(edges,Order)<>[12,12,12,12] then Error("A4 edge collapsed"); fi;
if Order(Q)<>60 or not ForAll([r,y,u,b],x->SignPerm(x)=1) then
  Error("image is not A5");
fi;
if u<>r^-1*b*y^-1 then Error("marked A5 recovery word changed"); fi;

Print("{\n");
Print("  \"all_relators_identity\": true,\n");
Print("  \"A4_edge_orders\": [12,12,12,12],\n");
Print("  \"S3_vertex_orders\": [6,6],\n");
Print("  \"image_is_A5\": true,\n");
Print("  \"image_order\": 60,\n");
Print("  \"u_recovery\": \"u=r^-1*b*y^-1\"\n");
Print("}\n");

