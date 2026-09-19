# Exact all-multiplicity collision test for the natural six-dimensional
# symplectic module of every marked Q1920 embedding in Sp6(2).

Read("experiments/atlas_a4_repeated_module_collision.g");;

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

ModuleOrbitProfile:=function(Q,V)
  return Collected(List(
      Filtered(ConjugacyClasses(Q),class->Representative(class) in V),
      class->[Size(class),Size(Group(Elements(class)))]));
end;;

# The outer A5 class in the point parabolic is the unique one whose radical
# has the marked Q1920 orbit/span profile.
sp:=Sp(6,2);;
field:=GF(2);;
point:=ImmutableVector(field,[One(field),Zero(field),Zero(field),
                              Zero(field),Zero(field),Zero(field)]);;
parabolic:=Stabilizer(sp,point,OnRight);;
radical:=PCore(parabolic,2);;
if Size(parabolic)<>23040 or Size(radical)<>32 or
   not IsElementaryAbelian(radical) then
  Error("unexpected Sp6(2) parabolic profile");
fi;
levi:=ComplementClassesRepresentatives(parabolic,radical)[1];;
a5Classes:=Filtered(ConjugacyClassesSubgroups(levi),class->
    Size(Representative(class))=60 and
    StructureDescription(Representative(class))="A5");;
qCandidates:=List(a5Classes,class->
    Group(Concatenation(GeneratorsOfGroup(radical),
                        GeneratorsOfGroup(Representative(class)))));;
qCandidates:=Filtered(qCandidates,Q->Size(Q)=1920 and
    ModuleOrbitProfile(Q,radical)=
      [ [ [ 1, 1 ], 1 ], [ [ 1, 2 ], 1 ], [ [ 15, 32 ], 2 ] ]);;
if Length(qCandidates)<>1 then
  Error("outer-A5 parabolic class is not unique");
fi;
spQ:=qCandidates[1];;
spNormalizer:=Normalizer(sp,spQ);;
spQAutomorphisms:=AutomorphismGroup(spQ);;
inducedAutomorphisms:=Set(List(Elements(spNormalizer),n->
    GroupHomomorphismByFunction(spQ,spQ,x->x^n)));;
inducedAutomorphismGroup:=Group(inducedAutomorphisms);;
embeddingTwists:=List(RightCosets(spQAutomorphisms,
                                  inducedAutomorphismGroup),Representative);;
if Length(embeddingTwists)<>4 then Error("expected four embedding twists"); fi;

AnalyzeMarking:=function(images,marking)
  local Q,iso,baseMapped,twistIndex,mapped;
  Q:=Group(images);
  iso:=IsomorphismGroups(Q,spQ);
  if iso=fail then Error("marked Q1920 did not transport to Sp6 parabolic"); fi;
  baseMapped:=List(images,g->Image(iso,g));
  for twistIndex in [1..Length(embeddingTwists)] do
    mapped:=List(baseMapped,g->Image(embeddingTwists[twistIndex],g));
    if Size(Group(mapped))<>1920 then Error("transport lost Q1920"); fi;
    AnalyzeRepeatedCollisionModule(mapped,
        ["Sp6-natural",marking,twistIndex]);
  od;
end;;

count:=0;;
for sub in LowIndexSubgroupsFpGroup(localUniversal,MAX_INDEX) do
  cosets:=RightCosets(localUniversal,sub);;
  action:=ActionHomomorphism(localUniversal,cosets,OnRight);;
  images:=List(localGenerators,g->Image(action,g));;
  r:=images[1];; y:=images[2];; u:=images[3];; b:=images[4];;
  edgeOrders:=[Size(Group([r^-1,b])),Size(Group([u,y])),
               Size(Group([u*r,y^-1])),Size(Group([r,b*y]))];;
  if Size(Group([r,u]))=6 and Size(Group([y,b]))=6 and
     edgeOrders=[12,12,12,12] and Size(Group(images))=1920 then
    count:=count+1;
    AnalyzeMarking(images,count);
  fi;
od;
if count<>2 then Error("expected exactly two marked Q1920 classes"); fi;
QUIT;
