# Universal small triangle completion for the first new large-component core
# edge over the A10 carrier.  J=<F,t> has order 288 in the A10 certificate,
# H=<F,u>=S3 x S3 has order 36, and <u,t>=A4 has order 12.

free := FreeGroup("r","z","c","t","u");;
r := free.1;; z := free.2;; c := free.3;; t := free.4;; u := free.5;;

# Exact four-generator presentation returned by
# IsomorphismFpGroupByGenerators(J,[r,z,c,t]) in GAP 4.14.
jRels := [
  c^2, z^3, t^3, r^3,
  c*t*c*t^-1,
  (t^-1*r^-1)^2,
  (c*z^-1)^2,
  c*r^-1*c*r,
  z^-1*r^-1*z*r,
  t*r*z^-1*t*z^-1*t^-1*z^-1
];;

hRels := [u^2,(u*r)^2,Comm(u,z),Comm(u,c)];;
edgeRel := (u*t^-1)^3;;
P := free/Concatenation(jRels,hRels,[edgeRel]);;

Print("attempting universal triangle order\n");
sizeP := Size(P);;
Print("P_order=",sizeP,"\n");
if sizeP <> infinity then
  gens := GeneratorsOfGroup(P);;
  rP:=gens[1];; zP:=gens[2];; cP:=gens[3];; tP:=gens[4];; uP:=gens[5];;
  Print("F_order=",Order(Subgroup(P,[rP,zP,cP])),
        " J_order=",Order(Subgroup(P,[rP,zP,cP,tP])),
        " H_order=",Order(Subgroup(P,[rP,zP,cP,uP])),
        " A4_order=",Order(Subgroup(P,[uP,tP])),"\n");
fi;

