# Low-index finite quotient search for the universal large K2,2 completion.

if not IsBound(MAX_INDEX) then MAX_INDEX:=16; fi;
free:=FreeGroup("r","y","u","b");;
r0:=free.1;; y0:=free.2;; u0:=free.3;; b0:=free.4;;
G:=free/[
  r0^3,y0^3,u0^2,b0^2,u0*r0*u0*r0,b0*y0*b0*y0,
  (r0^-1*b0)^3,(u0*y0)^3,((u0*r0)*y0^-1)^3,(r0*b0*y0)^3
];;
gg:=GeneratorsOfGroup(G);;
subs:=LowIndexSubgroupsFpGroup(G,MAX_INDEX);;
faithful:=[];;
for sub in subs do
  cosets:=RightCosets(G,sub);;
  action:=ActionHomomorphism(G,cosets,OnRight);;
  images:=List(gg,g->Image(action,g));;
  r:=images[1];; y:=images[2];; u:=images[3];; b:=images[4];;
  vertexOrders:=[Order(Group([r,u])),Order(Group([y,b]))];;
  edgeOrders:=[Order(Group([r^-1,b])),Order(Group([u,y])),
               Order(Group([u*r,y^-1])),Order(Group([r,b*y]))];;
  if vertexOrders=[6,6] and edgeOrders=[12,12,12,12] then
    Q:=Group(images);;
    Add(faithful,[Length(cosets),Order(Q),
                  List(images,p->ListPerm(p,Length(cosets)))]);;
  fi;
od;
Sort(faithful,function(left,right)
  return [left[1],left[2]]<[right[1],right[2]];
end);;
if Length(faithful)>0 then
  Print("SMALLEST_FAITHFUL degree=",faithful[1][1],
        " Q_order=",faithful[1][2],"\n");
  Print("images=",faithful[1][3],"\n");
fi;
Print("summary max_index=",MAX_INDEX," subgroups=",Length(subs),
      " faithful=",Length(faithful),
      " degree_order_histogram=",Collected(List(faithful,x->x{[1,2]})),"\n");
