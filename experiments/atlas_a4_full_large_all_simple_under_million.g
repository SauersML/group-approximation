# Enumerate every nonabelian finite simple group below 10^6 whose order is
# divisible by the rigorously forced 360, and screen the universal full-large
# rectangle for epimorphisms.  Set TARGET_INDEX before Read() to run one target;
# otherwise only print the complete target list.

free:=FreeGroup("r","z","c","u","t","s");;
r:=free.1;; z:=free.2;; c:=free.3;;
u:=free.4;; t:=free.5;; s:=free.6;;
b:=s*t;;
q:=t*c*s*c*t^-1*c*s*t*c;;

full:=free/[
  r^3,z^3,c^2,u^2,t^3,s^2,(s*t)^2,
  Comm(r,z),Comm(c,r),(c*z)^2,
  (u*r)^2,Comm(u,z),Comm(u,c),
  (c*t)^3,(u*t)^3,q,
  (r^-1*b)^3,(z*b)^3,
  ((u*r)*t)^3,(r*s)^3
];;

targets:=Filtered(
  AllSmallNonabelianSimpleGroups([1..999999]),
  g->Size(g) mod 360=0
);;
Print("targets=",List(targets,g->[StructureDescription(g),Size(g)]),"\n");

if IsBound(TARGET_INDEX) then
  ambient:=targets[TARGET_INDEX];;
  quotients:=GQuotients(full,ambient);;
  Print("target_index=",TARGET_INDEX,
        " target=",StructureDescription(ambient),
        " target_order=",Size(ambient),
        " epimorphism_classes=",Length(quotients),"\n");
fi;
QUIT;
