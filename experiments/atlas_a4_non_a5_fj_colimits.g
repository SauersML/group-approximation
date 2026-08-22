# Exact universal F'=S3xS3 / collision-J=S4 colimits for every non-A5
# faithful large-K2,2 coset image through degree twelve.

AnalyzeColimit:=function(marked)
  local Q,iso,fpQ,qgens,free,r,y,u,b,z,c,t,s,q,qRelations,
        seamRelations,P,images,ir,iy,iu,ib,iz,ic,it,is;
  Q:=Group(marked);
  iso:=IsomorphismFpGroupByGenerators(Q,marked);
  fpQ:=Image(iso);
  qgens:=FreeGeneratorsOfFpGroup(fpQ);
  if Length(qgens)<>4 then Error("marked fp presentation lost a generator"); fi;

  free:=FreeGroup("r","y","u","b","z","c");
  r:=free.1; y:=free.2; u:=free.3; b:=free.4;
  z:=free.5; c:=free.6; t:=y^-1; s:=b*y;
  q:=t*c*s*c*t^-1*c*s*t*c;
  qRelations:=List(RelatorsOfFpGroup(fpQ),
    rel->MappedWord(rel,qgens,[r,y,u,b]));
  seamRelations:=[
    z^3,c^2,Comm(r,z),Comm(c,r),(c*z)^2,Comm(u,z),Comm(u,c),
    (c*t)^3,q
  ];
  P:=free/Concatenation(qRelations,seamRelations);
  images:=GeneratorsOfGroup(P);
  ir:=images[1]; iy:=images[2]; iu:=images[3]; ib:=images[4];
  iz:=images[5]; ic:=images[6]; it:=iy^-1; is:=ib*iy;
  return [Length(qRelations),Size(P),
          Size(Group([ir,iy,iu,ib])),Size(Group([ir,iz,ic,iu])),
          Size(Group([it,is,ic])),Order(iz),Order(ic)];
end;;

MAX_INDEX:=12;;
freeLocal:=FreeGroup("r","y","u","b");;
r0:=freeLocal.1;; y0:=freeLocal.2;; u0:=freeLocal.3;; b0:=freeLocal.4;;
localUniversal:=freeLocal/[
  r0^3,y0^3,u0^2,b0^2,u0*r0*u0*r0,b0*y0*b0*y0,
  (r0^-1*b0)^3,(u0*y0)^3,((u0*r0)*y0^-1)^3,(r0*b0*y0)^3
];;
localGenerators:=GeneratorsOfGroup(localUniversal);;

records:=[];;
for sub in LowIndexSubgroupsFpGroup(localUniversal,MAX_INDEX) do
  cosets:=RightCosets(localUniversal,sub);;
  action:=ActionHomomorphism(localUniversal,cosets,OnRight);;
  marked:=List(localGenerators,g->Image(action,g));;
  r:=marked[1];; y:=marked[2];; u:=marked[3];; b:=marked[4];;
  t:=y^-1;; s:=b*y;; Q:=Group(marked);;
  edgeOrders:=[Size(Group([r^-1,b])),Size(Group([u,y])),
               Size(Group([u*r,y^-1])),Size(Group([r,b*y]))];;
  if Size(Group([r,u]))=6 and Size(Group([t,s]))=6 and
     edgeOrders=[12,12,12,12] and Size(Q) in [168,1920] and
     Size(Intersection(Group([r,u]),Group([t,s])))=1 and
     (not IsBound(ONLY_ORDER) or Size(Q)=ONLY_ORDER) then
    result:=AnalyzeColimit(marked);;
    Add(records,[Length(cosets),Size(Q),result]);
    Print("record=",records[Length(records)],"\n");
  fi;
od;
Print("fields=[coset_degree,local_order,[fp_relators,colimit_order,Q_image,F_image,J_image,z_order,c_order]]\n");
Print("histogram=",Collected(records),"\n");
QUIT;
