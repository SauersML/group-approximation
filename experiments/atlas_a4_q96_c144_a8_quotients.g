# Classify epimorphisms from the Q96--C144 cycle to A8 and certify the first
# faithful-vertex quotient.

free:=FreeGroup("r","z","c","u","t","s");;
r:=free.1;; z:=free.2;; c:=free.3;;
u:=free.4;; t:=free.5;; s:=free.6;;
b:=s*t;;
q:=t*c*s*c*t^-1*c*s*t*c;;

cycle:=free/[
  r^3,z^3,c^2,u^2,t^3,s^2,(s*t)^2,
  Comm(r,z),Comm(c,r),(c*z)^2,
  (u*r)^2,Comm(u,z),Comm(u,c),
  (c*t)^3,(u*t)^3,q,
  (r^-1*b)^3,(z*b)^3
];;

ambient:=AlternatingGroup(8);;
quotients:=GQuotients(cycle,ambient);;
histogram:=[];;
good:=[];;
largeCoreOrders:=[];;
for quotient in quotients do
  images:=List(GeneratorsOfGroup(cycle),g->Image(quotient,g));;
  ib:=images[6]*images[5];;
  orders:=[
    Size(Group(images{[1,2,3,4]})),
    Size(Group(images{[3,4,5]})),
    Size(Group(images{[5,6,3]})),
    Size(Group([images[1],images[2],ib]))
  ];;
  Add(histogram,orders);
  if orders=[36,96,24,144] then
    Add(good,images);
    y:=images[5]^-1;;
    Add(largeCoreOrders,List([
      images[1]^-1*ib,
      images[4]*y,
      images[4]*images[1]*y^-1,
      images[1]*ib*y
    ],Order));
  fi;
od;

if Length(quotients)<>24 then Error("unexpected A8 quotient count"); fi;
if Collected(histogram)<>[
  [[36,48,24,36],8],
  [[36,48,24,144],8],
  [[36,96,24,36],4],
  [[36,96,24,144],4]
] then Error("unexpected vertex-order histogram"); fi;
if Length(good)<>4 then Error("unexpected faithful quotient count"); fi;
if Collected(largeCoreOrders)<>[
  [[3,3,3,7],2],
  [[3,3,7,7],2]
] then Error("unexpected remaining large-core profile"); fi;

certificate:=List(good[1],p->ListPerm(p,8));;
if certificate<>[
  [2,4,7,1,5,3,6,8],
  [2,4,6,1,5,7,3,8],
  [6,3,2,7,8,1,4,5],
  [3,6,1,7,8,2,4,5],
  [1,2,5,7,8,4,6,3],
  [2,1,4,3,6,5,8,7]
] then Error("canonical certificate changed"); fi;
if Size(Group(good[1]))<>20160 then Error("certificate image is not A8"); fi;

Print("{\n");
Print("  \"ambient\": \"A8\",\n");
Print("  \"ambient_order\": 20160,\n");
Print("  \"epimorphism_classes\": ",Length(quotients),",\n");
Print("  \"faithful_vertex_classes\": ",Length(good),",\n");
Print("  \"faithful_vertex_orders\": [36, 96, 24, 144],\n");
Print("  \"large_core_order_profile\": ",Collected(largeCoreOrders),",\n");
Print("  \"certificate_generator_order\": [\"r\",\"z\",\"c\",\"u\",\"t\",\"s\"],\n");
Print("  \"certificate\": ",certificate,"\n");
Print("}\n");
QUIT;
