# Exact finite-simple quotient screen for the full large rectangle, collision,
# and forward fan.  Set TARGET_DEGREES before Read() to change A_n targets.

if not IsBound(TARGET_DEGREES) then TARGET_DEGREES:=[8,9,10]; fi;

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

for degree in TARGET_DEGREES do
  ambient:=AlternatingGroup(degree);;
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
  Print("target=A",degree,
        " target_order=",Size(ambient),
        " epimorphism_classes=",Length(quotients),
        " faithful_vertex_classes=",Length(good),
        " vertex_histogram=",Collected(histogram),"\n");
  if Length(good)>0 then
    Print("certificate_generator_order=[r,z,c,u,t,s]\n");
    Print("certificate=",List(good[1],p->ListPerm(p,degree)),"\n");
  fi;
od;
QUIT;
