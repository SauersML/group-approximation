# Exact transported-intersection audit for every faithful local large-K2,2
# coset image of degree at most 12.

if not IsBound(MAX_INDEX) then MAX_INDEX:=12; fi;
free:=FreeGroup("r","y","u","b");;
r0:=free.1;; y0:=free.2;; u0:=free.3;; b0:=free.4;;
G:=free/[
  r0^3,y0^3,u0^2,b0^2,u0*r0*u0*r0,b0*y0*b0*y0,
  (r0^-1*b0)^3,(u0*y0)^3,((u0*r0)*y0^-1)^3,(r0*b0*y0)^3
];;
gg:=GeneratorsOfGroup(G);;

# Exact marked collision S4.  This determines which of the three involutions
# in K=<t,s> is centralized by the collision involution c.
t4:=PermList([2,3,1,4]);;
s4:=PermList([2,1,3,4]);;
c4:=PermList([3,4,1,2]);;
collisionTranspositions:=[s4,t4*s4*t4^-1,t4^-1*s4*t4];;
collisionCentralFlags:=List(collisionTranspositions,d->IsOne(Comm(c4,d)));;
if Size(Group([t4,s4,c4]))<>24 or
   Number(collisionCentralFlags,x->x)<>1 then
  Error("marked collision S4 calibration failed");
fi;

subs:=LowIndexSubgroupsFpGroup(G,MAX_INDEX);;
records:=[];; survivors:=[];;
for sub in subs do
  cosets:=RightCosets(G,sub);;
  action:=ActionHomomorphism(G,cosets,OnRight);;
  images:=List(gg,g->Image(action,g));;
  r:=images[1];; y:=images[2];; u:=images[3];; b:=images[4];;
  t:=y^-1;; s:=b*t^-1;;
  vertexOrders:=[Size(Group([r,u])),Size(Group([y,b]))];;
  edgeOrders:=[Size(Group([r^-1,b])),Size(Group([u,y])),
               Size(Group([u*r,y^-1])),Size(Group([r,b*y]))];;
  if vertexOrders=[6,6] and edgeOrders=[12,12,12,12] then
    Q:=Group(images);;
    A:=Group([r,u]);; B:=Group([t,s]);; I:=Intersection(A,B);;
    label:=0;; compatible:=false;;
    if Size(I)=1 then
      compatible:=true;
    elif Size(I)=2 then
      d:=First(Elements(I),x->not IsOne(x));;
      localTranspositions:=[s,t*s*t^-1,t^-1*s*t];;
      label:=Position(localTranspositions,d);
      if label<>fail then compatible:=collisionCentralFlags[label]; fi;
    fi;
    record:=[Length(cosets),Size(Q),Size(I),label,compatible];;
    Add(records,record);
    if compatible then
      Add(survivors,[record,List(images,p->ListPerm(p,Length(cosets)))]);
    fi;
  fi;
od;

Print("collision_transposition_central_flags=",collisionCentralFlags,"\n");
Print("record_fields=[degree,image_order,intersection_order,B_involution_label,compatible]\n");
Print("record_histogram=",Collected(records),"\n");
Print("compatible_count=",Length(survivors),"\n");
for survivor in survivors do
  Print("compatible_record=",survivor[1]," images_[r,y,u,b]=",survivor[2],"\n");
od;
QUIT;
