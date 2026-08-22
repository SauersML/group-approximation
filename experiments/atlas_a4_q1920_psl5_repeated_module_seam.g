# Exact repeated-natural-module seam screen in characteristic two.
# The marked Q/Z embeds in PSL5(2); repeat its natural module BLOCKS times and
# solve the c,z equations inside the full linear A-centralizer.

if not IsBound(MARKING) then MARKING:=1; fi;
if not IsBound(EMBEDDING_CLASS) then EMBEDDING_CLASS:=1; fi;
if not IsBound(TWIST_INDEX) then TWIST_INDEX:=1; fi;
if not IsBound(BLOCKS) then BLOCKS:=2; fi;

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
  for generator in localGenerators do Add(tuple,Image(action,generator)); od;
  r:=tuple[1];; y:=tuple[2];; u:=tuple[3];; b:=tuple[4];;
  if Size(Group(tuple))=1920 and Size(Group([r,u]))=6 and
     Size(Group([y,b]))=6 and
     List([r^-1*b,u*y,(u*r)*y^-1,r*b*y],Order)=[3,3,3,3] then
    Add(markings,[Group(tuple),tuple]);
  fi;
od;
if Length(markings)<>2 then Error("expected two marked Q1920 classes"); fi;

originalQ:=markings[MARKING][1];;
naturalCenter:=NaturalHomomorphismByNormalSubgroup(originalQ,Center(originalQ));;
source:=Image(naturalCenter);;
marked:=List(markings[MARKING][2],g->Image(naturalCenter,g));;

linearAmbient:=SL(5,2);;
permutationMap:=IsomorphismPermGroup(linearAmbient);;
ambient:=Image(permutationMap);;
embeddings:=IsomorphicSubgroups(ambient,source);;
embedding:=embeddings[EMBEDDING_CLASS];;
imageQ:=Image(embedding);;
normalizer:=Normalizer(ambient,imageQ);;

PullbackConjugation:=function(normalizerElement)
  local generators,images;
  generators:=GeneratorsOfGroup(source);
  images:=List(generators,generator->PreImagesRepresentative(
      embedding,Image(embedding,generator)^normalizerElement));
  return GroupHomomorphismByImages(source,source,generators,images);
end;;

automorphisms:=AutomorphismGroup(source);;
induced:=Group(List(GeneratorsOfGroup(normalizer),PullbackConjugation),
               IdentityMapping(source));;
twists:=List(RightCosets(automorphisms,induced),Representative);;
alpha:=twists[TWIST_INDEX];;

transported:=List(marked,generator->Image(embedding,Image(alpha,generator)));;
linearTuple:=List(transported,permutation->
    PreImagesRepresentative(permutationMap,permutation));;

RepeatBlock:=function(current)
  local blockSize,totalSize,result,block,i,j;
  blockSize:=Length(current);
  totalSize:=BLOCKS*blockSize;
  result:=NullMat(totalSize,totalSize,GF(2));
  for block in [0..BLOCKS-1] do
    for i in [1..blockSize] do
      for j in [1..blockSize] do
        result[block*blockSize+i][block*blockSize+j]:=current[i][j];
      od;
    od;
  od;
  return ImmutableMatrix(GF(2),result);
end;;

r:=RepeatBlock(linearTuple[1]);;
y:=RepeatBlock(linearTuple[2]);;
u:=RepeatBlock(linearTuple[3]);;
b:=RepeatBlock(linearTuple[4]);;
t:=y^-1;; s:=b*y;;
dimension:=5*BLOCKS;;

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
adecomposition:=MTX.Indecomposition(GModuleByMats([r,u],GF(2)));;
bdecomposition:=MTX.Indecomposition(GModuleByMats([y,b],GF(2)));;
space:=VectorSpace(GF(2),List(basis,current->Flat(current)));;

if IsBound(NC_GROBNER) and NC_GROBNER then
  if BLOCKS<>1 then Error("NC_GROBNER uses the five-dimensional base module"); fi;
  if LoadPackage("GBNP")<>true then Error("GBNP is required"); fi;
  SetInfoLevel(InfoGBNP,0);
  freeAlgebra:=FreeAssociativeAlgebraWithOne(
      GF(2),"x0","x1","x2","x3","x4");;
  freeGenerators:=GeneratorsOfAlgebra(freeAlgebra);;
  freeOne:=freeGenerators[1];;
  variables:=freeGenerators{[2..6]};;
  freeZero:=Zero(freeAlgebra);;
  LiftScalarMatrix:=function(current)
    return List(current,row->List(row,entry->IntFFE(entry)*freeOne));
  end;;
  genericC:=List([1..5],i->List([1..5],j->
      Sum([1..5],k->IntFFE(basis[k][i][j])*variables[k])));;
  freeT:=LiftScalarMatrix(t);;
  freeS:=LiftScalarMatrix(s);;
  freeIdentity:=LiftScalarMatrix(IdentityMat(5,GF(2)));;
  relationMatrices:=[
    genericC*genericC+freeIdentity,
    (genericC*freeT)^3+freeIdentity,
    freeT*genericC*freeS*genericC*(freeT^2)*genericC*freeS*freeT*genericC+
        freeIdentity
  ];;
  freeRelations:=Filtered(Set(Concatenation(List(relationMatrices,
      current->Concatenation(current)))),entry->not IsZero(entry));;
  freeGb:=SGrobner(GP2NPList(freeRelations));;
  identityCoordinates:=SolutionMat(List(basis,current->Flat(current)),
      Flat(IdentityMat(5,GF(2))));;
  targetNormalForms:=List([1..5],index->StrongNormalFormNP(
      GP2NP(variables[index]+IntFFE(identityCoordinates[index])*freeOne),
      freeGb));;
  Print("marking=",MARKING,
      " embedding_class=",EMBEDDING_CLASS,
      " twist_index=",TWIST_INDEX,
      " twist_count=",Length(twists),
      " algebra_dimension=",Length(basis),
      " relation_count=",Length(freeRelations),
      " gb_count=",Length(freeGb),
      " identity_coordinates=",List(identityCoordinates,IntFFE),
      " identity_forced=",ForAll(targetNormalForms,current->current=[[],[]]),
      "\n");
  if IsBound(EXPORT_NC_GB) and EXPORT_NC_GB then
    GBNP.ConfigPrint("x0","x1","x2","x3","x4");
    Print("groebner_basis=\n");
    PrintNPList(freeGb);
    Print("identity_normal_forms=\n");
    PrintNPList(targetNormalForms);
  fi;
  FORCE_QUIT_GAP(0);
fi;

centralizer:=[];;
for coordinates in Elements(space) do
  current:=ImmutableMatrix(GF(2),List([0..dimension-1],index->
      coordinates{[index*dimension+1..(index+1)*dimension]}));
  if RankMat(current)=dimension then Add(centralizer,current); fi;
od;

candidates:=Filtered(centralizer,c->
    Order(c)=2 and Order(c*t)=3 and
    IsOne(t*c*s*c*t^-1*c*s*t*c));;
zCandidates:=Filtered(centralizer,z->Order(z)=3 and IsOne((z*b)^3));;
fullCandidates:=[];;
for c in candidates do
  for z in zCandidates do
    if IsOne((c*z)^2) and
       [Size(Group([r,z,c,u])),Size(Group([t,s,c])),Size(Group([r,z,b]))]
          =[36,24,144] then
      Add(fullCandidates,[c,z]);
    fi;
  od;
od;

if IsBound(EXPORT_BASE) and EXPORT_BASE then
  Print("base_tuple_r_y_u_b=",List([r,y,u,b],matrix->
      List(matrix,row->List(row,IntFFE))),"\n");
  Print("centralizer_algebra_basis=",List(basis,matrix->
      List(matrix,row->List(row,IntFFE))),"\n");
fi;

Print("marking=",MARKING,
      " embedding_class=",EMBEDDING_CLASS,
      " twist_index=",TWIST_INDEX,
      " twist_count=",Length(twists),
      " blocks=",BLOCKS,
      " dimension=",dimension,
      " A_indecomposables=",List(adecomposition,pair->pair[2].dimension),
      " B_indecomposables=",List(bdecomposition,pair->pair[2].dimension),
      " algebra_dimension=",Length(basis),
      " centralizer_order=",Length(centralizer),
      " collision_candidates=",Length(candidates),
      " forward_z_candidates=",Length(zCandidates),
      " full_candidates=",Length(fullCandidates),"\n");
QUIT;
