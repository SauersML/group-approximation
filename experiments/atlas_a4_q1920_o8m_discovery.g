# Structural discovery of Q1920 slices in the singular parabolic of
# Omega_8^-(2), after the plus-type and symplectic hosts fail.

MAX_INDEX:=12;;
free:=FreeGroup("r","y","u","b");;
r0:=free.1;; y0:=free.2;; u0:=free.3;; b0:=free.4;;
localUniversal:=free/[
  r0^3,y0^3,u0^2,b0^2,u0*r0*u0*r0,b0*y0*b0*y0,
  (r0^-1*b0)^3,(u0*y0)^3,((u0*r0)*y0^-1)^3,(r0*b0*y0)^3
];;
localGenerators:=GeneratorsOfGroup(localUniversal);;

ModuleProfile:=function(H,V)
  local orbits;
  orbits:=Orbits(H,Elements(V),OnPoints);
  return Collected(List(orbits,orbit->[Length(orbit),Size(Group(orbit))]));
end;;

field:=GF(2);;
ambient:=Omega(-1,8,2);;
vectorSpace:=VectorSpace(field,IdentityMat(8,field));;
nonzero:=Filtered(Elements(vectorSpace),v->not IsZero(v));;
vectorOrbits:=Orbits(ambient,nonzero,OnRight);;
Print("ambient_order=",Size(ambient)," vector_orbit_sizes=",
      List(vectorOrbits,Length),"\n");

qCandidates:=[];;
for orbit in vectorOrbits do
  parabolic:=Stabilizer(ambient,orbit[1],OnRight);;
  radical:=PCore(parabolic,2);;
  Print("orbit_stabilizer_[orbit,P,O2]=",
        [Length(orbit),Size(parabolic),Size(radical)],"\n");
  if Size(radical)=64 and IsElementaryAbelian(radical) then
    complements:=ComplementClassesRepresentatives(parabolic,radical);;
    Print("complement_orders=",List(complements,Size),"\n");
    for levi in complements do
      a5Classes:=Filtered(ConjugacyClassesSubgroups(levi),class->
          Size(Representative(class))=60 and
          StructureDescription(Representative(class))="A5");;
      subspaces:=Filtered(SubgroupsSolvableGroup(radical),V->Size(V)=32);;
      records:=[];;
      for class in a5Classes do
        H:=Representative(class);;
        invariant:=Filtered(subspaces,V->
            ForAll(GeneratorsOfGroup(H),g->V^g=V));;
        matched:=Filtered(invariant,V->ModuleProfile(H,V)=
            [ [ [ 1, 1 ], 1 ], [ [ 1, 2 ], 1 ], [ [ 15, 32 ], 2 ] ]);
        Add(records,[Length(invariant),Length(matched)]);
        Append(qCandidates,List(matched,V->
            Group(Concatenation(GeneratorsOfGroup(V),
                                GeneratorsOfGroup(H)))));
      od;
      Print("levi_[order,a5classes,invariant32_matched]=",
            [Size(levi),Length(a5Classes),records],"\n");
    od;
  fi;
od;

qCandidates:=Set(qCandidates);;
qRepresentatives:=[];;
for Q in qCandidates do
  if not ForAny(qRepresentatives,R->IsConjugate(ambient,Q,R)) then
    Add(qRepresentatives,Q);
  fi;
od;
if Length(qRepresentatives)<>1 then Error("matching Q class is not unique"); fi;
ambientQ:=qRepresentatives[1];;
qNormalizer:=Normalizer(ambient,ambientQ);;
qAutomorphisms:=AutomorphismGroup(ambientQ);;
inducedAutomorphisms:=Set(List(Elements(qNormalizer),n->
    GroupHomomorphismByFunction(ambientQ,ambientQ,x->x^n)));;
inducedAutomorphismGroup:=Group(inducedAutomorphisms);;
embeddingTwists:=List(RightCosets(qAutomorphisms,
                                  inducedAutomorphismGroup),Representative);;
Print("q_[classes,normalizer,aut,induced,twists]=",
      [Length(qRepresentatives),Size(qNormalizer),Size(qAutomorphisms),
       Size(inducedAutomorphismGroup),Length(embeddingTwists)],"\n");

AnalyzeMarking:=function(images,markingIndex)
  local Q,iso,baseMapped,mapped,twist,r,y,u,b,t,s,A,centralizer,
        candidates,c,collisionWord,orderThree,z,seamPairs,profiles,
        totalCollision,totalSeams,completionOrders,twistIndex;
  Q:=Group(images);
  iso:=IsomorphismGroups(Q,ambientQ);
  if iso=fail then Error("marked Q1920 did not transport to Omega8-"); fi;
  baseMapped:=List(images,g->Image(iso,g));
  profiles:=[]; totalCollision:=0; totalSeams:=0; completionOrders:=[];
  twistIndex:=0;
  for twist in embeddingTwists do
    twistIndex:=twistIndex+1;
    mapped:=List(baseMapped,g->Image(twist,g));
    if IsBound(EXPORT_MODULE_MATRICES) and EXPORT_MODULE_MATRICES then
      Print("module_matrices=",List(mapped,g->List(g,row->
          List(row,IntFFE))),"\n");
    fi;
    if IsBound(AnalyzeRepeatedCollisionModule) then
      AnalyzeRepeatedCollisionModule(mapped,["O8-",markingIndex,twistIndex]);
    fi;
    r:=mapped[1]; y:=mapped[2]; u:=mapped[3]; b:=mapped[4];
    t:=y^-1; s:=b*y; A:=Group([r,u]);
    centralizer:=Centralizer(ambient,A);
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
    AnalyzeMarking(images,count);
  fi;
od;
Print("marking_count=",count,"\n");
QUIT;
