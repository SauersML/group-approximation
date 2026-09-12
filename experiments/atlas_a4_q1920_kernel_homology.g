# Exact Reidemeister-Schreier abelianization of the index-60 kernel of the
# canonical Q1920 seam map to Q/V=A5.

MAX_INDEX:=12;;
freeLocal:=FreeGroup("r","y","u","b");;
r0:=freeLocal.1;; y0:=freeLocal.2;; u0:=freeLocal.3;; b0:=freeLocal.4;;
localUniversal:=freeLocal/[
  r0^3,y0^3,u0^2,b0^2,u0*r0*u0*r0,b0*y0*b0*y0,
  (r0^-1*b0)^3,(u0*y0)^3,((u0*r0)*y0^-1)^3,(r0*b0*y0)^3
];;
localGenerators:=GeneratorsOfGroup(localUniversal);;

AnalyzeMarking:=function(marked,action)
  local Q,normals,V,qQuotient,qMap,iso,fpQ,qgens,free,r,y,u,b,z,c,t,s,q,
        qRelations,seamRelations,P,pGenerators,targetImages,phi,kernel,
        retraction,
        quotientElements,quotientImages,allRelations,freeGenerators,
        BoundaryVector,relationRows,baseRank,cycleDimension,pVWords,
        pVcWords,pCenterWord,vRows,vcRows,seamRows,centerRows,joinRows,
        dimV,dimVc,dimJoin,rel,start,quotientElement,qLift,qLiftWord,
        InverseLetters,cOrbitRows,zOrbitRows,cOrbitDim,zOrbitDim;
  Q:=Group(marked);
  V:=First(NormalSubgroups(Q),n->Size(n)=32 and IsElementaryAbelian(n));
  qQuotient:=Q/V;
  qMap:=NaturalHomomorphismByNormalSubgroup(Q,V);
  iso:=IsomorphismFpGroupByGenerators(Q,marked);
  fpQ:=Image(iso);
  qgens:=FreeGeneratorsOfFpGroup(fpQ);

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
  pGenerators:=GeneratorsOfGroup(P);
  Print("P_abelian_invariants=",AbelianInvariants(P),"\n");
  targetImages:=Concatenation(List(marked,g->Image(qMap,g)),
                              [One(qQuotient),One(qQuotient)]);
  phi:=GroupHomomorphismByImages(P,qQuotient,pGenerators,targetImages);
  if not IsGroupHomomorphism(phi) or Size(Image(phi))<>60 then
    Error("canonical A5 quotient failed");
  fi;
  retraction:=GroupHomomorphismByImages(P,Q,pGenerators,
      Concatenation(marked,[One(Q),One(Q)]));
  if not IsGroupHomomorphism(retraction) or Size(Image(retraction))<>1920 then
    Error("Q retraction failed");
  fi;
  kernel:=Kernel(phi);
  Print("Q_retraction_image_order=",Size(Image(retraction)),"\n");
  Print("kernel_profile_[index,generators,abelian_invariants]=",
        [Index(P,kernel),Length(GeneratorsOfGroup(kernel)),
         AbelianInvariants(kernel)],"\n");

  # Compute H_1(N,F_2) directly from the 60-sheeted presentation cover.
  # This also gives explicit images of chosen kernel words without asking GAP
  # for a second, expensive coset presentation of N.
  quotientElements:=Elements(qQuotient);
  quotientImages:=targetImages;
  freeGenerators:=GeneratorsOfGroup(free);
  allRelations:=Concatenation(qRelations,seamRelations);
  BoundaryVector:=function(word,start)
    local vector,state,letter,generator,position;
    vector:=ListWithIdenticalEntries(6*Length(quotientElements),Zero(GF(2)));
    state:=start;
    for letter in word do
      generator:=AbsInt(letter);
      if letter<0 then state:=state*quotientImages[generator]^-1; fi;
      position:=Position(quotientElements,state);
      vector[6*(position-1)+generator]:=
          vector[6*(position-1)+generator]+One(GF(2));
      if letter>0 then state:=state*quotientImages[generator]; fi;
    od;
    return vector;
  end;
  relationRows:=[];
  for rel in allRelations do
    for start in quotientElements do
      Add(relationRows,BoundaryVector(
          LetterRepAssocWord(rel,freeGenerators),start));
    od;
  od;
  baseRank:=RankMat(relationRows);
  cycleDimension:=6*Length(quotientElements)-Length(quotientElements)+1;
  Print("cover_homology_[cycle_dim,relator_rank,h1_dim]=",
        [cycleDimension,baseRank,cycleDimension-baseRank],"\n");

  pVWords:=List(GeneratorsOfGroup(V),vg->LetterRepAssocWord(
      UnderlyingElement(PreImagesRepresentative(action,vg)),
      FreeGeneratorsOfFpGroup(localUniversal)));
  pVcWords:=List(pVWords,word->Concatenation([-6],word,[6]));
  pCenterWord:=LetterRepAssocWord(UnderlyingElement(
      PreImagesRepresentative(action,GeneratorsOfGroup(Centre(Q))[1])),
      FreeGeneratorsOfFpGroup(localUniversal));
  vRows:=List(pVWords,word->BoundaryVector(word,One(qQuotient)));
  vcRows:=List(pVcWords,word->BoundaryVector(word,One(qQuotient)));
  seamRows:=[BoundaryVector([5],One(qQuotient)),
             BoundaryVector([6],One(qQuotient))];
  centerRows:=[BoundaryVector(pCenterWord,One(qQuotient))];
  dimV:=RankMat(Concatenation(relationRows,vRows))-baseRank;
  dimVc:=RankMat(Concatenation(relationRows,vcRows))-baseRank;
  joinRows:=Concatenation(vRows,vcRows);
  dimJoin:=RankMat(Concatenation(relationRows,joinRows))-baseRank;
  Print("Nab_subspaces_log2_[V,Vc,VcapVc,seam,center,VjoinVc,alljoin]=",
        [dimV,dimVc,dimV+dimVc-dimJoin,
         RankMat(Concatenation(relationRows,seamRows))-baseRank,
         RankMat(Concatenation(relationRows,centerRows))-baseRank,
         dimJoin,
         RankMat(Concatenation(relationRows,joinRows,seamRows))-baseRank],
        "\n");

  # Close the c- and z-lines under the quotient A5 action.  Arbitrary Q-lifts
  # suffice: two lifts differ by V<=N, whose conjugation is inner on N_ab.
  InverseLetters:=word->List(Reversed(word),letter->-letter);
  cOrbitRows:=[];
  zOrbitRows:=[];
  for quotientElement in quotientElements do
    qLift:=PreImagesRepresentative(qMap,quotientElement);
    qLiftWord:=LetterRepAssocWord(UnderlyingElement(
        PreImagesRepresentative(action,qLift)),
        FreeGeneratorsOfFpGroup(localUniversal));
    Add(cOrbitRows,BoundaryVector(Concatenation(
        InverseLetters(qLiftWord),[6],qLiftWord),One(qQuotient)));
    Add(zOrbitRows,BoundaryVector(Concatenation(
        InverseLetters(qLiftWord),[5],qLiftWord),One(qQuotient)));
  od;
  cOrbitDim:=RankMat(Concatenation(relationRows,cOrbitRows))-baseRank;
  zOrbitDim:=RankMat(Concatenation(relationRows,zOrbitRows))-baseRank;
  Print("Nab_A5_orbits_[c,z,Vcap<cA5>,Vcap<zA5>,Vplusc,Vplusz]=",
        [cOrbitDim,zOrbitDim,
         dimV+cOrbitDim-(RankMat(Concatenation(
             relationRows,vRows,cOrbitRows))-baseRank),
         dimV+zOrbitDim-(RankMat(Concatenation(
             relationRows,vRows,zOrbitRows))-baseRank),
         RankMat(Concatenation(relationRows,vRows,cOrbitRows))-baseRank,
         RankMat(Concatenation(relationRows,vRows,zOrbitRows))-baseRank],
        "\n");
end;;

count:=0;;
for sub in LowIndexSubgroupsFpGroup(localUniversal,MAX_INDEX) do
  cosets:=RightCosets(localUniversal,sub);;
  action:=ActionHomomorphism(localUniversal,cosets,OnRight);;
  marked:=[];;
  for generator in localGenerators do
    Add(marked,Image(action,generator));
  od;
  r:=marked[1];; y:=marked[2];; u:=marked[3];; b:=marked[4];;
  edgeOrders:=[Size(Group([r^-1,b])),Size(Group([u,y])),
               Size(Group([u*r,y^-1])),Size(Group([r,b*y]))];;
  if Size(Group([r,u]))=6 and Size(Group([y,b]))=6 and
     edgeOrders=[12,12,12,12] and Size(Group(marked))=1920 then
    count:=count+1;
    Print("=== marking ",count," ===\n");
    AnalyzeMarking(marked,action);
  fi;
od;
Print("marking_count=",count,"\n");
QUIT;
