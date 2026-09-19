# Marked seam census inside the only simple groups below 10^7 which contain
# Q1920 or its central quotient.  Set TARGET_INDEX in [1..5].

if not IsBound(TARGET_INDEX) then Error("set TARGET_INDEX in [1..5]"); fi;

targetConstructors:=[
  ["PSL(3,4)",function() return PSL(3,4); end],
  ["M22",function() return MathieuGroup(22); end],
  ["O(7,2)",function() return Sp(6,2); end],
  ["PSU(4,3)",function() return PSU(4,3); end],
  ["PSL(5,2)",function() return PSL(5,2); end]
];;

# Recover the two exact marked Q1920 classes from the complete degree-twelve
# local census.
free:=FreeGroup("r","y","u","b");;
r0:=free.1;; y0:=free.2;; u0:=free.3;; b0:=free.4;;
localUniversal:=free/[
  r0^3,y0^3,u0^2,b0^2,u0*r0*u0*r0,b0*y0*b0*y0,
  (r0^-1*b0)^3,(u0*y0)^3,((u0*r0)*y0^-1)^3,(r0*b0*y0)^3
];;
localGenerators:=GeneratorsOfGroup(localUniversal);;
markings:=[];;
for subgroup in LowIndexSubgroupsFpGroup(localUniversal,12) do
  cosets:=RightCosets(localUniversal,subgroup);;
  action:=ActionHomomorphism(localUniversal,cosets,OnRight);;
  tuple:=[];;
  for generator in localGenerators do
    Add(tuple,Image(action,generator));
  od;
  r:=tuple[1];; y:=tuple[2];; u:=tuple[3];; b:=tuple[4];;
  if Size(Group(tuple))=1920 and Size(Group([r,u]))=6 and
     Size(Group([y,b]))=6 and
     List([r^-1*b,u*y,(u*r)*y^-1,r*b*y],Order)=[3,3,3,3] then
    Add(markings,[Group(tuple),tuple]);
  fi;
od;
if Length(markings)<>2 then Error("expected two marked Q1920 classes"); fi;

entry:=targetConstructors[TARGET_INDEX];;
targetName:=entry[1];;
ambient:=Image(IsomorphismPermGroup(entry[2]()));;

PullbackConjugation:=function(source,embedding,normalizerElement)
  local generators,images;
  generators:=GeneratorsOfGroup(source);
  images:=List(generators,generator->PreImagesRepresentative(
      embedding,Image(embedding,generator)^normalizerElement));
  return GroupHomomorphismByImages(source,source,generators,images);
end;;

MarkingProfile:=function(markingNumber,imageOrder)
  local originalQ,originalTuple,natural,source,marked,embeddings,embedding,
        imageQ,normalizer,automorphisms,induced,inducedGenerators,coset,
        alpha,transported,r,y,u,b,t,s,A,centralizer,candidates,c,z,
        collisionCandidates,fullCandidates,centralizerSizes,normalizerIndices,
        vertexOrders;
  originalQ:=markings[markingNumber][1];
  originalTuple:=markings[markingNumber][2];
  if imageOrder=1920 then
    source:=originalQ;
    marked:=originalTuple;
  else
    natural:=NaturalHomomorphismByNormalSubgroup(originalQ,Center(originalQ));
    source:=Image(natural);
    marked:=List(originalTuple,generator->Image(natural,generator));
  fi;

  embeddings:=IsomorphicSubgroups(ambient,source);
  collisionCandidates:=0;
  fullCandidates:=0;
  centralizerSizes:=[];
  normalizerIndices:=[];
  automorphisms:=AutomorphismGroup(source);
  for embedding in embeddings do
    imageQ:=Image(embedding);
    normalizer:=Normalizer(ambient,imageQ);
    inducedGenerators:=List(GeneratorsOfGroup(normalizer),
        element->PullbackConjugation(source,embedding,element));
    induced:=Group(inducedGenerators,IdentityMapping(source));
    Add(normalizerIndices,Index(automorphisms,induced));
    for coset in RightCosets(automorphisms,induced) do
      alpha:=Representative(coset);
      transported:=List(marked,generator->Image(
          embedding,Image(alpha,generator)));
      r:=transported[1];; y:=transported[2];;
      u:=transported[3];; b:=transported[4];;
      t:=y^-1;; s:=b*y;;
      A:=Group([r,u]);;
      centralizer:=Centralizer(ambient,A);
      Add(centralizerSizes,Size(centralizer));
      candidates:=Filtered(Elements(centralizer),element->
          Order(element)=2 and Order(element*t)=3 and
          IsOne(t*element*s*element*t^-1*element*s*t*element));
      collisionCandidates:=collisionCandidates+Length(candidates);
      for c in candidates do
        for z in Filtered(Elements(centralizer),element->Order(element)=3) do
          if IsOne((c*z)^2) and IsOne((z*b)^3) then
            vertexOrders:=[Size(Group([r,z,c,u])),
                           Size(Group([t,s,c])),
                           Size(Group([r,z,b]))];
            if vertexOrders=[36,24,144] then
              fullCandidates:=fullCandidates+1;
            fi;
          fi;
        od;
      od;
    od;
  od;
  return rec(
    marking:=markingNumber,
    imageOrder:=imageOrder,
    embeddingClasses:=Length(embeddings),
    normalizerIndices:=normalizerIndices,
    centralizerSizeHistogram:=Collected(centralizerSizes),
    collisionCandidates:=collisionCandidates,
    fullCandidates:=fullCandidates
  );
end;;

profiles:=[];;
for markingNumber in [1..2] do
  for imageOrder in [960,1920] do
    Add(profiles,MarkingProfile(markingNumber,imageOrder));
  od;
od;

Print("target_index=",TARGET_INDEX,
      " target=",targetName,
      " order=",Size(ambient),"\n");
for profile in profiles do Print(profile,"\n"); od;
QUIT;
