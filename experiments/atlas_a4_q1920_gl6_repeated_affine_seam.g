# Universal collision coefficient algebra on repeated copies of every faithful
# six-dimensional homogeneous affine Q1920 module over F2.
#
# Parameters:
#   MARKING          one of the two faithful large-K2,2 marked Q1920 quotients
#   COMPLEMENT_CLASS one of the four conjugacy classes of A5 complements
#   EXPORT_NC_GB     print the exact noncommutative Groebner certificate

if not IsBound(MARKING) then MARKING:=1; fi;
if not IsBound(COMPLEMENT_CLASS) then COMPLEMENT_CLASS:=1; fi;
if LoadPackage("GBNP")<>true then Error("GBNP is required"); fi;
SetInfoLevel(InfoGBNP,0);

free:=FreeGroup("r","y","u","b");;
r0:=free.1;; y0:=free.2;; u0:=free.3;; b0:=free.4;;
universal:=free/[
  r0^3,y0^3,u0^2,b0^2,u0*r0*u0*r0,b0*y0*b0*y0,
  (r0^-1*b0)^3,(u0*y0)^3,((u0*r0)*y0^-1)^3,(r0*b0*y0)^3
];;
universalGenerators:=GeneratorsOfGroup(universal);;

markedTuples:=[];;
for subgroup in LowIndexSubgroupsFpGroup(universal,12) do
  cosets:=RightCosets(universal,subgroup);;
  action:=ActionHomomorphism(universal,cosets,OnRight);;
  images:=[];;
  for generator in universalGenerators do
    Add(images,Image(action,generator));
  od;
  r:=images[1];; y:=images[2];; u:=images[3];; b:=images[4];;
  edgeOrders:=[Size(Group([r^-1,b])),Size(Group([u,y])),
               Size(Group([u*r,y^-1])),Size(Group([r,b*y]))];;
  if Size(Group([r,u]))=6 and Size(Group([y,b]))=6 and
     edgeOrders=[12,12,12,12] and Size(Group(images))=1920 then
    Add(markedTuples,images);
  fi;
od;
if Length(markedTuples)<>2 then
  Error("expected exactly two faithful order-1920 marked quotients");
fi;
if not MARKING in [1..2] then Error("MARKING must be 1 or 2"); fi;
images:=markedTuples[MARKING];;
Q:=Group(images);;

normalSubgroups:=NormalSubgroups(Q);;
radicals:=Filtered(normalSubgroups,subgroup->Size(subgroup)=32 and
    IsElementaryAbelian(subgroup));;
if Length(radicals)<>1 then Error("expected a unique elementary-abelian 2^5 radical"); fi;
V:=radicals[1];;
if not IsNormal(Q,V) or Size(Q/V)<>60 or not IsSimpleGroup(Q/V) then
  Error("characteristic 2^5 radical calibration failed");
fi;
complements:=ComplementClassesRepresentatives(Q,V);;
if Length(complements)<>4 then Error("expected four A5 complement classes"); fi;
if not COMPLEMENT_CLASS in [1..4] then
  Error("COMPLEMENT_CLASS must be between 1 and 4");
fi;
complement:=complements[COMPLEMENT_CLASS];;
if Size(complement)<>60 or Size(Intersection(complement,V))<>1 then
  Error("complement calibration failed");
fi;

pcgs:=Pcgs(V);;
moduleRank:=Length(pcgs);;
if moduleRank<>5 then Error("expected a rank-five affine radical"); fi;

HomogeneousMatrix:=function(generator)
  local linearRows,conjugate,linear,complementPart,translation,
        affineTranslation,rows,index;
  linearRows:=[];
  for conjugate in List(pcgs,basisElement->basisElement^generator) do
    Add(linearRows,ExponentsOfPcElement(pcgs,conjugate));
  od;
  linear:=ImmutableMatrix(GF(2),List(linearRows,row->
      List(row,entry->entry*One(GF(2)))));
  complementPart:=First(Elements(complement),candidate->
      generator*candidate^-1 in V);
  if complementPart=fail then Error("affine complement decomposition failed"); fi;
  translation:=ImmutableMatrix(GF(2),[
      List(ExponentsOfPcElement(pcgs,generator*complementPart^-1),entry->
          entry*One(GF(2)))
  ]);
  affineTranslation:=translation*linear;
  rows:=[];
  for index in [1..moduleRank] do
    Add(rows,Concatenation(linear[index],[Zero(GF(2))]));
  od;
  Add(rows,Concatenation(affineTranslation[1],[One(GF(2))]));
  return ImmutableMatrix(GF(2),rows);
end;;

tuple:=List(images,HomogeneousMatrix);;
r:=tuple[1];; y:=tuple[2];; u:=tuple[3];; b:=tuple[4];;
t:=y^-1;; s:=b*y;;
calibrationWords:=[r^3,y^3,u^2,b^2,u*r*u*r,b*y*b*y,
    (r^-1*b)^3,(u*y)^3,((u*r)*y^-1)^3,(r*b*y)^3];;
if Size(Group(tuple))<>1920 or not ForAll(calibrationWords,IsOne) then
  Print("generated_order=",Size(Group(tuple)),
      " calibration_orders=",List(calibrationWords,Order),"\n");
  Error("homogeneous affine tuple calibration failed");
fi;

MatrixFromCoordinates:=function(coordinates,basis)
  local result,index;
  result:=Zero(basis[1]);
  for index in [1..Length(basis)] do
    result:=result+coordinates[index]*basis[index];
  od;
  return ImmutableMatrix(GF(2),result);
end;;

CentralizerAlgebraBasis:=function(generators)
  local n,matrixBasis,i,j,current,rows,nullBasis;
  n:=Length(generators[1]);
  matrixBasis:=[];
  for i in [1..n] do
    for j in [1..n] do
      current:=NullMat(n,n,GF(2));
      current[i][j]:=One(GF(2));
      Add(matrixBasis,ImmutableMatrix(GF(2),current));
    od;
  od;
  rows:=List(matrixBasis,current->Flat(List(generators,
      generator->current*generator-generator*current)));
  nullBasis:=NullspaceMat(rows);
  return List(nullBasis,coordinates->
      MatrixFromCoordinates(coordinates,matrixBasis));
end;;

basis:=CentralizerAlgebraBasis([r,u]);;
basisSize:=Length(basis);;
names:=List([0..basisSize-1],index->Concatenation("x",String(index)));;
freeAlgebra:=CallFuncList(FreeAssociativeAlgebraWithOne,
    Concatenation([GF(2)],names));;
freeGenerators:=GeneratorsOfAlgebra(freeAlgebra);;
freeOne:=freeGenerators[1];;
variables:=freeGenerators{[2..basisSize+1]};;

LiftScalarMatrix:=function(current)
  return List(current,row->List(row,entry->IntFFE(entry)*freeOne));
end;;

genericC:=List([1..6],i->List([1..6],j->
    Sum([1..basisSize],k->IntFFE(basis[k][i][j])*variables[k])));;
freeT:=LiftScalarMatrix(t);;
freeS:=LiftScalarMatrix(s);;
freeIdentity:=LiftScalarMatrix(IdentityMat(6,GF(2)));;
baseMatrices:=[genericC*genericC+freeIdentity,
              (genericC*freeT)^3+freeIdentity];;
baseRelations:=Filtered(Set(Concatenation(List(baseMatrices,
    current->Concatenation(current)))),entry->not IsZero(entry));;
baseGb:=SGrobner(GP2NPList(baseRelations));;

collisionMatrix:=
    freeT*genericC*freeS*genericC*(freeT^2)*genericC*freeS*freeT*genericC+
        freeIdentity;;
collisionRelations:=Filtered(Set(Concatenation(collisionMatrix)),
    entry->not IsZero(entry));;
reducedCollision:=Set(List(GP2NPList(collisionRelations),current->
    StrongNormalFormNP(current,baseGb)));;
reducedCollision:=Filtered(reducedCollision,current->current<>[[],[]]);;
fullGb:=SGrobner(Concatenation(baseGb,reducedCollision));;

identityCoordinates:=SolutionMat(List(basis,current->Flat(current)),
    Flat(IdentityMat(6,GF(2))));;
targetNormalForms:=List([1..basisSize],index->StrongNormalFormNP(
    GP2NP(variables[index]+IntFFE(identityCoordinates[index])*freeOne),
    fullGb));;
identityForced:=ForAll(targetNormalForms,current->current=[[],[]]);;

Print("marking=",MARKING,
    " complement_class=",COMPLEMENT_CLASS,
    " generated_order=",Size(Group(tuple)),
    " centralizer_algebra_dimension=",basisSize,
    " base_relation_count=",Length(baseRelations),
    " base_gb_count=",Length(baseGb),
    " reduced_collision_count=",Length(reducedCollision),
    " full_gb_count=",Length(fullGb),
    " identity_coordinates=",List(identityCoordinates,IntFFE),
    " identity_forced=",identityForced,"\n");
Print("RESULT marking=",MARKING," complement_class=",COMPLEMENT_CLASS,
    " identity_forced=",identityForced,"\n");
if IsBound(EXPORT_NC_GB) and EXPORT_NC_GB then
  CallFuncList(GBNP.ConfigPrint,names);
  Print("basis_matrices=",List(basis,current->List(current,row->
      List(row,IntFFE))),"\n");
  Print("tuple_matrices=",List(tuple,current->List(current,row->
      List(row,IntFFE))),"\n");
  Print("base_groebner_basis=\n");
  PrintNPList(baseGb);
  Print("collision_remainders_mod_base=\n");
  PrintNPList(reducedCollision);
  Print("full_groebner_basis=\n");
  PrintNPList(fullGb);
  Print("identity_normal_forms=\n");
  PrintNPList(targetNormalForms);
fi;
QUIT;
