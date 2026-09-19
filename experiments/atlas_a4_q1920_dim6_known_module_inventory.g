# Exact isomorphism and Loewy-profile inventory for the currently known
# faithful six-dimensional F2[Q1920] modules: homogeneous affine modules and
# the natural symplectic-parabolic module.

MAX_INDEX:=12;;
Reset(GlobalMersenneTwister,1);;
Reset(GlobalRandomSource,1);;

free:=FreeGroup("r","y","u","b");;
r0:=free.1;; y0:=free.2;; u0:=free.3;; b0:=free.4;;
localUniversal:=free/[
  r0^3,y0^3,u0^2,b0^2,u0*r0*u0*r0,b0*y0*b0*y0,
  (r0^-1*b0)^3,(u0*y0)^3,((u0*r0)*y0^-1)^3,(r0*b0*y0)^3
];;
localGenerators:=GeneratorsOfGroup(localUniversal);;

markedTuples:=[];;
for subgroup in LowIndexSubgroupsFpGroup(localUniversal,MAX_INDEX) do
  cosets:=RightCosets(localUniversal,subgroup);;
  action:=ActionHomomorphism(localUniversal,cosets,OnRight);;
  images:=List(localGenerators,g->Image(action,g));;
  r:=images[1];; y:=images[2];; u:=images[3];; b:=images[4];;
  edgeOrders:=[Size(Group([r^-1,b])),Size(Group([u,y])),
               Size(Group([u*r,y^-1])),Size(Group([r,b*y]))];;
  if Size(Group([r,u]))=6 and Size(Group([y,b]))=6 and
     edgeOrders=[12,12,12,12] and Size(Group(images))=1920 then
    Add(markedTuples,images);
  fi;
od;
if Length(markedTuples)<>2 then
  Error("expected exactly two marked Q1920 classes");
fi;

ModuleOrbitProfile:=function(Q,V)
  return Collected(List(
      Filtered(ConjugacyClasses(Q),class->Representative(class) in V),
      class->[Size(class),Size(Group(Elements(class)))]));
end;;

sp:=Sp(6,2);;
point:=ImmutableVector(GF(2),[One(GF(2)),Zero(GF(2)),Zero(GF(2)),
                              Zero(GF(2)),Zero(GF(2)),Zero(GF(2))]);;
parabolic:=Stabilizer(sp,point,OnRight);;
spRadical:=PCore(parabolic,2);;
levi:=ComplementClassesRepresentatives(parabolic,spRadical)[1];;
a5Classes:=Filtered(ConjugacyClassesSubgroups(levi),class->
    Size(Representative(class))=60 and
    StructureDescription(Representative(class))="A5");;
qCandidates:=List(a5Classes,class->
    Group(Concatenation(GeneratorsOfGroup(spRadical),
                        GeneratorsOfGroup(Representative(class)))));;
qCandidates:=Filtered(qCandidates,Q->Size(Q)=1920 and
    ModuleOrbitProfile(Q,spRadical)=
      [ [ [ 1, 1 ], 1 ], [ [ 1, 2 ], 1 ], [ [ 15, 32 ], 2 ] ]);;
if Length(qCandidates)<>1 then Error("unique symplectic Q failed"); fi;
spQ:=qCandidates[1];;
spNormalizer:=Normalizer(sp,spQ);;
spAut:=AutomorphismGroup(spQ);;
inducedAut:=Group(Set(List(Elements(spNormalizer),n->
    GroupHomomorphismByFunction(spQ,spQ,x->x^n))));;
spTwists:=List(RightCosets(spAut,inducedAut),Representative);;
if Length(spTwists)<>4 then Error("expected four symplectic twists"); fi;

HomogeneousMatrix:=function(generator,complement,pcgs)
  local linearRows,conjugate,linear,complementPart,translation,
        affineTranslation,rows,index;
  linearRows:=[];
  for conjugate in List(pcgs,basisElement->basisElement^generator) do
    Add(linearRows,ExponentsOfPcElement(pcgs,conjugate));
  od;
  linear:=ImmutableMatrix(GF(2),List(linearRows,row->
      List(row,entry->entry*One(GF(2)))));
  complementPart:=First(Elements(complement),candidate->
      generator*candidate^-1 in Group(pcgs));
  if complementPart=fail then Error("affine complement decomposition failed"); fi;
  translation:=ImmutableMatrix(GF(2),[
      List(ExponentsOfPcElement(pcgs,generator*complementPart^-1),entry->
          entry*One(GF(2))) ]);
  affineTranslation:=translation*linear;
  rows:=[];
  for index in [1..Length(pcgs)] do
    Add(rows,Concatenation(linear[index],[Zero(GF(2))]));
  od;
  Add(rows,Concatenation(affineTranslation[1],[One(GF(2))]));
  return ImmutableMatrix(GF(2),rows);
end;;

DualTuple:=function(tuple)
  return List(tuple,generator->ImmutableMatrix(GF(2),
      TransposedMat(generator^-1)));
end;;

ModuleProfile:=function(tuple,radicalGenerators,z)
  local identity,differences,firstRows,horizontal,fixedRows,secondRows,fixedDimension,
        radicalImageDimension,radicalSquareDimension,centralRank,module;
  identity:=IdentityMat(6,GF(2));
  differences:=List(radicalGenerators,g->g-identity);
  firstRows:=Concatenation(List(differences,RowsOfMatrix));
  radicalImageDimension:=RankMat(firstRows);
  secondRows:=Concatenation(List(Cartesian(differences,differences),pair->
      RowsOfMatrix(pair[1]*pair[2])));
  radicalSquareDimension:=RankMat(secondRows);
  horizontal:=List([1..6],i->Concatenation(List(differences,current->
      current[i])));
  fixedRows:=NullspaceMat(ImmutableMatrix(GF(2),horizontal));
  fixedDimension:=Length(fixedRows);
  centralRank:=RankMat(z-identity);
  module:=GModuleByMats(tuple,GF(2));
  return [fixedDimension,radicalImageDimension,radicalSquareDimension,
      centralRank,List(MTX.CompositionFactors(module),factor->factor.dimension),
      List(MTX.Indecomposition(module),pair->pair[2].dimension)];
end;;

IsomorphismMatrix:=function(modules)
  return List(modules,left->List(modules,right->
      MTX.IsomorphismModules(left,right)<>fail));
end;;

for markingIndex in [1..2] do
  images:=markedTuples[markingIndex];;
  Q:=Group(images);;
  radical:=First(NormalSubgroups(Q),subgroup->Size(subgroup)=32 and
      IsElementaryAbelian(subgroup));;
  pcgs:=Pcgs(radical);;
  centerGenerator:=First(GeneratorsOfGroup(Center(Q)),g->not IsOne(g));;
  complements:=ComplementClassesRepresentatives(Q,radical);;
  affineTuples:=List(complements,complement->List(images,g->
      HomogeneousMatrix(g,complement,pcgs)));;
  affineDualTuples:=List(affineTuples,DualTuple);;

  iso:=IsomorphismGroups(Q,spQ);;
  if iso=fail then Error("symplectic transport failed"); fi;
  spTuples:=List(spTwists,twist->List(images,g->
      Image(twist,Image(iso,g))));;

  allTuples:=Concatenation(affineTuples,affineDualTuples,spTuples);;
  labels:=Concatenation(
      List([1..4],i->Concatenation("affine-",String(i))),
      List([1..4],i->Concatenation("affine-dual-",String(i))),
      List([1..4],i->Concatenation("symplectic-",String(i))));;
  modules:=List(allTuples,tuple->GModuleByMats(tuple,GF(2)));;
  profiles:=[];
  for tupleIndex in [1..Length(allTuples)] do
    target:=Group(allTuples[tupleIndex]);;
    eval:=GroupHomomorphismByImages(Q,target,images,allTuples[tupleIndex]);;
    if eval=fail or Size(Image(eval))<>1920 then Error("tuple map failed"); fi;
    Add(profiles,ModuleProfile(allTuples[tupleIndex],
        List(GeneratorsOfGroup(radical),g->Image(eval,g)),
        Image(eval,centerGenerator)));
  od;
  Print("DIM6_KNOWN marking=",markingIndex,
      " labels=",labels,"\n");
  Print("DIM6_PROFILES_[Vfix,VM,J2M,rank(z-1),composition,indecomp]=",
      profiles,"\n");
  Print("DIM6_ISOMORPHISM_MATRIX=",IsomorphismMatrix(modules),"\n");
od;
QUIT;
