# Exact test of the canonical rank-two escape suggested by the moved-module
# theorem: Q1920 inside the 2^5:S6 parabolic of Sp6(2).

MAX_INDEX:=12;;
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

# Build the canonical parabolic and select the outer-A5 module class.
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
      [ [ [ 1, 1 ], 1 ], [ [ 1, 2 ], 1 ], [ [ 15, 32 ], 2 ] ]);
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
Print("sp_order=",Size(sp)," parabolic_order=",Size(parabolic),
      " levi_order=",Size(levi)," a5_class_count=",Length(a5Classes),
      " matched_q_count=",Length(qCandidates),
      " q_normalizer_order=",Size(spNormalizer),
      " aut_q_order=",Size(spQAutomorphisms),
      " induced_aut_order=",Size(inducedAutomorphismGroup),
      " embedding_twist_count=",Length(embeddingTwists),"\n");

AnalyzeMarking:=function(images)
  local Q,iso,baseMapped,mapped,r,y,u,b,t,s,A,centralizer,candidates,c,
        collisionWord,orderThree,z,seamPairs,twist,profiles,totalCollision,
        totalSeams,completionOrders;
  Q:=Group(images);
  iso:=IsomorphismGroups(Q,spQ);
  if iso=fail then Error("marked Q1920 did not transport to Sp6 parabolic"); fi;
  baseMapped:=List(images,g->Image(iso,g));
  profiles:=[]; totalCollision:=0; totalSeams:=0; completionOrders:=[];
  for twist in embeddingTwists do
    mapped:=List(baseMapped,g->Image(twist,g));
    r:=mapped[1]; y:=mapped[2]; u:=mapped[3]; b:=mapped[4];
    t:=y^-1; s:=b*y; A:=Group([r,u]);
    centralizer:=Centralizer(sp,A);
    candidates:=[];
    for c in Elements(centralizer) do
      if Order(c)=2 then
        collisionWord:=t*c*s*c*t^-1*c*s*t*c;
        if IsOne((c*t)^3) and IsOne(collisionWord) and
           Size(Group([t,s,c]))=24 and
           StructureDescription(Group([t,s,c]))="S4" then
          Add(candidates,c);
        fi;
      fi;
    od;
    orderThree:=Filtered(Elements(centralizer),z->Order(z)=3);
    seamPairs:=[];
    for c in candidates do
      for z in orderThree do
        if c*z*c=z^-1 and Size(Group([c,z]))=6 then
          Add(seamPairs,[c,z]);
        fi;
      od;
    od;
    Add(profiles,[Size(centralizer),Length(candidates),Length(seamPairs)]);
    totalCollision:=totalCollision+Length(candidates);
    totalSeams:=totalSeams+Length(seamPairs);
    if Length(seamPairs)>0 then
      Add(completionOrders,Size(Group(Concatenation(mapped,seamPairs[1]))));
    fi;
  od;
  Print("embedding_profile_[centralizer,collision,seam]_histogram=",
        Collected(profiles),"\n");
  Print("total_collision_count=",totalCollision,
        " total_seam_count=",totalSeams,
        " completion_orders=",completionOrders,"\n");
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
    Print("=== marking ",count," ===\n");
    AnalyzeMarking(images);
  fi;
od;
Print("marking_count=",count,"\n");
QUIT;
