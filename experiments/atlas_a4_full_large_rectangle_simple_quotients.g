# Exact finite-simple quotient screen for the full large rectangle, collision,
# and forward fan.

free:=FreeGroup("r","z","c","u","t","s");;
r:=free.1;; z:=free.2;; c:=free.3;;
u:=free.4;; t:=free.5;; s:=free.6;;
b:=s*t;; y:=t^-1;;
q:=t*c*s*c*t^-1*c*s*t*c;;

full:=free/[
  r^3,z^3,c^2,u^2,t^3,s^2,(s*t)^2,
  Comm(r,z),Comm(c,r),(c*z)^2,
  (u*r)^2,Comm(u,z),Comm(u,c),
  (c*t)^3,(u*t)^3,q,
  (r^-1*b)^3,(z*b)^3,
  ((u*r)*t)^3,(r*s)^3
];;

targets:=[
  ["A8",AlternatingGroup(8)],
  ["A9",AlternatingGroup(9)],
  ["A10",AlternatingGroup(10)],
  ["PSL3(4)",PSL(3,4)],
  ["PSU3(3)",PSU(3,3)],
  ["PSp4(3)",PSp(4,3)],
  ["M11",MathieuGroup(11)],
  ["M12",MathieuGroup(12)],
  ["Sp6(2)",Image(IsomorphismPermGroup(Sp(6,2)))]
];;

for target in targets do
  name:=target[1];; ambient:=target[2];;
  quotients:=GQuotients(full,ambient);;
  good:=[];; histogram:=[];;
  for quotient in quotients do
    images:=List(GeneratorsOfGroup(full),g->Image(quotient,g));;
    ir:=images[1];; iz:=images[2];; ic:=images[3];;
    iu:=images[4];; it:=images[5];; is:=images[6];; ib:=is*it;;
    orders:=[
      Size(Group([ir,iu,it,is])),
      Size(Group([ir,iz,ic,iu])),
      Size(Group([it,is,ic])),
      Size(Group([ir,iz,ib]))
    ];;
    Add(histogram,orders);
    if orders=[60,36,24,144] then Add(good,images); fi;
  od;
  Print("target=",name,
        " target_order=",Size(ambient),
        " epimorphism_classes=",Length(quotients),
        " faithful_vertex_classes=",Length(good),
        " vertex_histogram=",Collected(histogram),"\n");
  if Length(good)>0 then
    Print("certificate_generator_order=[r,z,c,u,t,s]\n");
    Print("certificate=",List(good[1],p->ListPerm(p,LargestMovedPoint(ambient))),"\n");
  fi;
od;
QUIT;
