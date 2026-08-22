# Exact test for a finite completion in which the added seam S3 acts by
# automorphisms of a marked Q1920 and fixes its first radial S3 pointwise.

MAX_INDEX:=12;;
free:=FreeGroup("r","y","u","b");;
r0:=free.1;; y0:=free.2;; u0:=free.3;; b0:=free.4;;
G:=free/[
  r0^3,y0^3,u0^2,b0^2,u0*r0*u0*r0,b0*y0*b0*y0,
  (r0^-1*b0)^3,(u0*y0)^3,((u0*r0)*y0^-1)^3,(r0*b0*y0)^3
];;
gg:=GeneratorsOfGroup(G);;

ComposeAutomorphisms:=function(outer,inner)
  local candidates,source;
  source:=Source(outer);
  candidates:=Set([outer*inner,inner*outer]);
  return First(candidates,map->ForAll(GeneratorsOfGroup(source),g->
      Image(map,g)=Image(outer,Image(inner,g))));
end;;

PairMultiply:=function(left,right)
  return [left[1]*Image(left[2],right[1]),
          ComposeAutomorphisms(left[2],right[2])];
end;;

PairProduct:=function(letters,identity)
  local value,letter;
  value:=identity;
  for letter in letters do value:=PairMultiply(value,letter); od;
  return value;
end;;

PairPower:=function(value,n,identity)
  local result,i;
  result:=identity;
  for i in [1..n] do result:=PairMultiply(result,value); od;
  return result;
end;;

PairInverse:=function(value)
  return [Image(value[2]^-1,value[1]^-1),value[2]^-1];
end;;

AnalyzeMarking:=function(images)
  local Q,r,y,u,b,t,s,aut,pointwise,candidates,alpha,orderThree,
        one,c,tPair,sPair,collisionWord,dihedralPairs,identity,centralizer,
        q0,delta,inner,alphaOptions,pair,zPair,faithfulCandidates;
  Q:=Group(images);
  r:=images[1]; y:=images[2]; u:=images[3]; b:=images[4];
  t:=y^-1; s:=b*y; one:=One(Q);
  aut:=AutomorphismGroup(Q);
  Print("aut_order=",Size(aut),"\n");
  pointwise:=Filtered(Elements(aut),map->Image(map,r)=r and Image(map,u)=u);
  Print("pointwise_A_order=",Length(pointwise),
        " order_histogram=",Collected(List(pointwise,Order)),"\n");
  identity:=[one,One(aut)];

  # Every holomorph element centralizing A induces one of the pointwise-A
  # automorphisms delta.  Recover its unique affine pair (q0,alpha) from
  # delta(g)=q0*alpha(g)*q0^-1.
  centralizer:=[];
  for q0 in Elements(Q) do
    inner:=InnerAutomorphism(Q,q0);
    for delta in pointwise do
      alphaOptions:=Set([delta*inner,inner*delta]);
      alpha:=First(alphaOptions,map->ForAll(GeneratorsOfGroup(Q),g->
          q0*Image(map,g)*q0^-1=Image(delta,g)));
      if alpha=fail then Error("automorphism composition calibration failed"); fi;
      pair:=[q0,alpha];
      if not pair in centralizer then Add(centralizer,pair); fi;
    od;
  od;
  Print("holomorph_pointwise_A_order=",Length(centralizer),
        " order_histogram=",Collected(List(centralizer,pair->
          First([1..120],n->PairPower(pair,n,identity)=identity))),"\n");

  candidates:=[];
  tPair:=[t,One(aut)]; sPair:=[s,One(aut)];
  for c in centralizer do
    if PairPower(c,2,identity)=identity then
      collisionWord:=PairProduct([
        tPair,c,sPair,c,[t^-1,One(aut)],c,sPair,tPair,c],identity);
      if PairPower(PairMultiply(c,tPair),3,identity)=identity and
         collisionWord=identity then
        Add(candidates,c);
      fi;
    fi;
  od;
  faithfulCandidates:=Filtered(candidates,pair->pair<>identity);
  Print("collision_holomorph_count=",Length(candidates),
        " identity_flags=",List(candidates,pair->pair=identity),
        " nontrivial_count=",Length(faithfulCandidates),"\n");
  orderThree:=Filtered(centralizer,pair->PairPower(pair,3,identity)=identity and
                                         pair<>identity);
  dihedralPairs:=[];
  for c in faithfulCandidates do
    for zPair in orderThree do
      if PairProduct([c,zPair,PairInverse(c)],identity)=PairInverse(zPair) then
        Add(dihedralPairs,[c,zPair]);
      fi;
    od;
  od;
  Print("seam_S3_holomorph_pair_count=",Length(dihedralPairs),"\n");
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
