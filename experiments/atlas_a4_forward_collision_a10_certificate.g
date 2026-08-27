# Exact degree-ten permutation certificate for the minimal forward-collision
# quotient.  The lists are one-based images, in generator order r,z,c,t,s.

r := PermList([1,3,5,6,2,7,4,8,9,10]);;
z := PermList([1,3,5,7,2,4,6,8,9,10]);;
c := PermList([1,4,6,2,7,3,5,8,10,9]);;
t := PermList([1,2,5,4,9,7,10,8,3,6]);;
s := PermList([2,1,3,8,9,6,10,4,5,7]);;
b := s*t;;
q := t*c*s*c*t^-1*c*s*t*c;;

rels := [
  r^3, z^3, Comm(z,r),
  c^2, Comm(c,r), c*z*c*z,
  t^3, s^2, (s*t)^2,
  (r^-1*b)^3, (z*b)^3,
  q
];;

Q := Group([r,z,c,t,s]);;
A := Group([r,z]);;
B := Group([b]);;
C := Group([r,z,b]);;
F := Group([r,z,c]);;
K := Group([t,s]);;

if not ForAll(rels, IsOne) then Error("a defining relator survives"); fi;
if Order(A) <> 9 then Error("A is not injected"); fi;
if Order(B) <> 2 then Error("B is not injected"); fi;
if Order(C) <> 144 then Error("C is not injected"); fi;
if Order(F) <> 18 then Error("F is not injected"); fi;
if Order(K) <> 6 then Error("K is not injected"); fi;
if Order(Q) <> 1814400 then Error("unexpected image order"); fi;
if not ForAll([r,z,c,t,s], permutation -> SignPerm(permutation)=1) then
  Error("image is not contained in A10");
fi;

Print("{\n");
Print("  \"all_relators_identity\": true,\n");
Print("  \"degree\": 10,\n");
Print("  \"edge_group_orders\": {\"A\": 9, \"B\": 2},\n");
Print("  \"image_is_A10\": true,\n");
Print("  \"image_order\": ", Order(Q), ",\n");
Print("  \"vertex_group_orders\": {\"C\": ", Order(C),
      ", \"F\": ", Order(F), ", \"K\": ", Order(K), "}\n");
Print("}\n");

