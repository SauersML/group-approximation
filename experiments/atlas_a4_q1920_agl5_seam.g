# Exact seam test in the affine normalizer of the characteristic module
# V=C2^5 of each marked Q1920.  This allows the added seam to move Q while
# retaining V, unlike the narrower Hol(Q) test.

MAX_INDEX:=12;;
free:=FreeGroup("r","y","u","b");;
r0:=free.1;; y0:=free.2;; u0:=free.3;; b0:=free.4;;
G:=free/[
  r0^3,y0^3,u0^2,b0^2,u0*r0*u0*r0,b0*y0*b0*y0,
  (r0^-1*b0)^3,(u0*y0)^3,((u0*r0)*y0^-1)^3,(r0*b0*y0)^3
];;
gg:=GeneratorsOfGroup(G);;

AnalyzeMarking:=function(images)
  local Q,normals,V,A,representatives,complements,K0,q,K,cosets,action,
        affineImages,r,y,u,b,t,s,affineV,affineA,AGL,centralizer,candidates,
        c,collisionWord,orderThree,z,seamPairs;
  Q:=Group(images);
  normals:=NormalSubgroups(Q);
  V:=First(normals,n->Size(n)=32 and IsElementaryAbelian(n));
  A:=Group([images[1],images[3]]);
  representatives:=ComplementClassesRepresentatives(Q,V);
  complements:=Set(Concatenation(List(representatives,K0->
      List(Elements(Q),q->K0^q))));
  K:=First(complements,H->IsSubgroup(H,A));
  if K=fail then Error("no A-containing A5 complement"); fi;
  Print("complement_count=",Length(complements),
        " A_containing_count=",Number(complements,H->IsSubgroup(H,A)),"\n");

  cosets:=RightCosets(Q,K);
  action:=ActionHomomorphism(Q,cosets,OnRight);
  affineImages:=List(images,g->Image(action,g));
  r:=affineImages[1]; y:=affineImages[2];
  u:=affineImages[3]; b:=affineImages[4];
  t:=y^-1; s:=b*y;
  affineV:=Image(action,V);
  affineA:=Group([r,u]);
  if Size(affineV)<>32 or not IsTransitive(affineV,[1..32]) then
    Error("module is not regular in complement action");
  fi;

  AGL:=Normalizer(SymmetricGroup(32),affineV);
  Print("affine_normalizer_order=",Size(AGL),"\n");
  centralizer:=Centralizer(AGL,affineA);
  Print("affine_pointwise_A_centralizer_order=",Size(centralizer),
        " order_histogram=",Collected(List(Elements(centralizer),Order)),"\n");
  candidates:=[];
  for c in Elements(centralizer) do
    if Order(c)=2 then
      collisionWord:=t*c*s*c*t^-1*c*s*t*c;
      if IsOne((c*t)^3) and IsOne(collisionWord) then Add(candidates,c); fi;
    fi;
  od;
  Print("nontrivial_collision_involution_count=",Length(candidates),"\n");
  orderThree:=Filtered(Elements(centralizer),z->Order(z)=3);
  seamPairs:=[];
  for c in candidates do
    for z in orderThree do
      if c*z*c=z^-1 then Add(seamPairs,[c,z]); fi;
    od;
  od;
  Print("faithful_seam_S3_pair_count=",Length(seamPairs),"\n");
end;;

count:=0;;
for sub in LowIndexSubgroupsFpGroup(G,MAX_INDEX) do
  cosets:=RightCosets(G,sub);;
  action:=ActionHomomorphism(G,cosets,OnRight);;
  images:=List(gg,g->Image(action,g));;
  r:=images[1];; y:=images[2];; u:=images[3];; b:=images[4];;
  edgeOrders:=[Size(Group([r^-1,b])),Size(Group([u,y])),
               Size(Group([u*r,y^-1])),Size(Group([r,b*y]))];;
  if Size(Group([r,u]))=6 and Size(Group([y,b]))=6 and
     edgeOrders=[12,12,12,12] and Size(Group(images))=1920 then
    count:=count+1;
    Print("=== marking ",count," ===\n");
    AnalyzeMarking(images);
  fi;
od;
Print("marking_count=",count,"\n");
QUIT;
