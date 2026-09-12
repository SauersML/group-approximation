# Exact finite completion of the collision/core three-edge triangle.

free := FreeGroup("c", "u", "t");;
c := free.1;; u := free.2;; t := free.3;;

Q := free / [
  c^2, u^2, t^3,
  Comm(c,u),
  (c*t)^3,
  (u*t)^3
];;

V4 := Subgroup(Q,[Q.1,Q.2]);;
A4c := Subgroup(Q,[Q.1,Q.3]);;
A4u := Subgroup(Q,[Q.2,Q.3]);;

if Size(Q) <> 96 then Error("triangle completion did not have order 96"); fi;
if Size(V4) <> 4 then Error("V4 edge failed to inject"); fi;
if Size(A4c) <> 12 then Error("collision A4 edge failed to inject"); fi;
if Size(A4u) <> 12 then Error("core A4 edge failed to inject"); fi;

Print("{\n");
Print("  \"group_order\": ",Size(Q),",\n");
Print("  \"structure\": \"",StructureDescription(Q),"\",\n");
Print("  \"commuting_involution_edge_order\": ",Size(V4),",\n");
Print("  \"collision_A4_edge_order\": ",Size(A4c),",\n");
Print("  \"core_A4_edge_order\": ",Size(A4u),"\n");
Print("}\n");
QUIT;
