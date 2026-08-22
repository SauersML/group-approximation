# Exact six-generator presentation for the first C144 cycle beyond Q96.
# Set MAX_INDEX before Read() to change the bounded low-index screen.

if not IsBound(MAX_INDEX) then MAX_INDEX := 16; fi;

# Calibrate the marked collision quotient independently before using it as a
# vertex.  Adding the Q96 edge relation (ct)^3 to K=<t,s> and q gives S4.
jFree := FreeGroup("jt", "js", "jc");;
jt:=jFree.1;; js:=jFree.2;; jc:=jFree.3;;
jq:=jt*jc*js*jc*jt^-1*jc*js*jt*jc;;
jVertex:=jFree/[jt^3,js^2,jc^2,(js*jt)^2,(jc*jt)^3,jq];;
if Size(jVertex)<>24 then Error("marked collision S4 calibration failed"); fi;

free := FreeGroup("r", "z", "c", "u", "t", "s");;
r := free.1;; z := free.2;; c := free.3;;
u := free.4;; t := free.5;; s := free.6;;
b := s*t;;
q := t*c*s*c*t^-1*c*s*t*c;;

cycle := free / [
  # F'=S3(r,u) x S3(z,c).
  r^3, z^3, c^2, u^2,
  Comm(r,z), Comm(c,r), (c*z)^2,
  (u*r)^2, Comm(u,z), Comm(u,c),

  # J=S4 collision quotient and Q96 triangle.
  t^3, s^2, (s*t)^2,
  (c*t)^3, (u*t)^3, q,

  # C=C2^4:C3^2 attached along <r,z> and <b=s*t>.
  (r^-1*b)^3, (z*b)^3
];;

generators := GeneratorsOfGroup(cycle);;
lowIndexSubgroups := LowIndexSubgroupsFpGroup(cycle,MAX_INDEX);;
Print("max_index=",MAX_INDEX,
      " low_index_subgroups=",Length(lowIndexSubgroups),"\n");

for subgroup in lowIndexSubgroups do
  cosets := RightCosets(cycle,subgroup);;
  action := ActionHomomorphism(cycle,cosets,OnRight);;
  image := Image(action);;
  images := List(generators,generator->Image(action,generator));;
  ir:=images[1];; iz:=images[2];; ic:=images[3];;
  iu:=images[4];; it:=images[5];; is:=images[6];; ib:=is*it;;
  orders := [
    Size(Group([ir,iz,ic,iu])),
    Size(Group([ic,iu,it])),
    Size(Group([it,is,ic])),
    Size(Group([ir,iz,ib]))
  ];;
  if orders=[36,96,24,144] then
    Print("FAITHFUL_CYCLE degree=",Length(cosets),
          " image_order=",Size(image)," vertex_orders=",orders,"\n");
    Print("generator_images_one_based=",
          List(images,p->ListPerm(p,Length(cosets))),"\n");
  fi;
od;
QUIT;
