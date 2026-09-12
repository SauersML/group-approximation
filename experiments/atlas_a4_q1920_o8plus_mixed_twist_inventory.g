# Exact restriction inventory for the two Omega8+(2) embedding twists.
# The discovery file calls AnalyzeRepeatedCollisionModule once per twist; this
# lightweight callback compares the pair before that file exits.

Read("experiments/atlas_a4_repeated_module_collision.g");;

A4DirectSumMatrix:=function(left,right)
  local n,m,zeroLeft,zeroRight,rows,i;
  n:=Length(left); m:=Length(right);
  zeroLeft:=ListWithIdenticalEntries(n,Zero(GF(2)));
  zeroRight:=ListWithIdenticalEntries(m,Zero(GF(2)));
  rows:=[];
  for i in [1..n] do Add(rows,Concatenation(left[i],zeroRight)); od;
  for i in [1..m] do Add(rows,Concatenation(zeroLeft,right[i])); od;
  return ImmutableMatrix(GF(2),rows);
end;;

A4TwistInventory:=[];;

A4AnalyzeMixedV4:=function(tuple,label)
  local r,y,u,b,t,s,d,n,basis,basisSize,names,freeAlgebra,
        freeGenerators,freeOne,variables,liftScalarMatrix,genericC,freeT,
        freeIdentity,relationMatrices,relations,fullGb,identityCoordinates,
        targetNormalForms,identityForced;
  r:=tuple[1]; y:=tuple[2]; u:=tuple[3]; b:=tuple[4];
  t:=y^-1; s:=b*y; d:=s*t^-1; n:=Length(r);
  if Size(Group([r,u,d]))<>48 then Error("unexpected L order"); fi;
  basis:=A4CentralizerAlgebraBasis([r,u,d]);
  basisSize:=Length(basis);
  if not ForAll(basis,current->current*r=r*current and
      current*u=u*current and current*d=d*current) then
    Error("L-centralizer basis audit failed");
  fi;
  names:=List([0..basisSize-1],index->Concatenation("x",String(index)));
  freeAlgebra:=CallFuncList(FreeAssociativeAlgebraWithOne,
      Concatenation([GF(2)],names));
  freeGenerators:=GeneratorsOfAlgebra(freeAlgebra);
  freeOne:=freeGenerators[1];
  variables:=freeGenerators{[2..basisSize+1]};
  liftScalarMatrix:=function(current)
    return List(current,row->List(row,entry->IntFFE(entry)*freeOne));
  end;
  genericC:=List([1..n],i->List([1..n],j->
      Sum([1..basisSize],k->IntFFE(basis[k][i][j])*variables[k])));
  freeT:=liftScalarMatrix(t);
  freeIdentity:=liftScalarMatrix(IdentityMat(n,GF(2)));
  relationMatrices:=[genericC*genericC+freeIdentity,
      genericC*(freeT^2)*genericC*freeT+
          freeT*genericC*(freeT^2)];
  relations:=Filtered(Set(Concatenation(List(relationMatrices,
      current->Concatenation(current)))),entry->not IsZero(entry));
  Print("MIXED_V4_BASE label=",label,
      " module_dimension=",n,
      " L_centralizer_dimension=",basisSize,
      " relation_count=",Length(relations),"\n");
  fullGb:=SGrobner(GP2NPList(relations));
  identityCoordinates:=SolutionMat(List(basis,current->Flat(current)),
      Flat(IdentityMat(n,GF(2))));
  targetNormalForms:=List([1..basisSize],index->StrongNormalFormNP(
      GP2NP(variables[index]+IntFFE(identityCoordinates[index])*freeOne),
      fullGb));
  identityForced:=ForAll(targetNormalForms,current->current=[[],[]]);
  Print("MIXED_V4_RESULT label=",label,
      " gb_count=",Length(fullGb),
      " identity_coordinates=",List(identityCoordinates,IntFFE),
      " identity_forced=",identityForced,"\n");
  if IsBound(EXPORT_MIXED_V4_NC_GB) and EXPORT_MIXED_V4_NC_GB then
    CallFuncList(GBNP.ConfigPrint,names);
    Print("MIXED_V4_CERTIFICATE label=",label,"\n");
    Print("full_groebner_basis=\n");
    PrintNPList(fullGb);
    Print("identity_normal_forms=\n");
    PrintNPList(targetNormalForms);
  fi;
  return rec(label:=label,moduleDimension:=n,
      centralizerDimension:=basisSize,relationCount:=Length(relations),
      fullGb:=fullGb,identityCoordinates:=identityCoordinates,
      identityForced:=identityForced);
end;;

AnalyzeRepeatedCollisionModule:=function(tuple,label)
  local r,y,u,b,t,s,d,aBasis,lBasis,aModule,lModule,marking,combined,
        combinedA,combinedL,combinedQ,individualLDimensions,crossHomDimension;
  r:=tuple[1]; y:=tuple[2]; u:=tuple[3]; b:=tuple[4];
  t:=y^-1; s:=b*y; d:=s*t^-1;
  if Size(Group([r,u,d]))<>48 then Error("unexpected twist L order"); fi;
  aBasis:=A4CentralizerAlgebraBasis([r,u]);
  lBasis:=A4CentralizerAlgebraBasis([r,u,d]);
  aModule:=GModuleByMats([r,u],GF(2));
  lModule:=GModuleByMats([r,u,d],GF(2));
  Print("TWIST_INVENTORY label=",label,
      " A_centralizer_dimension=",Length(aBasis),
      " L_order=48",
      " L_centralizer_dimension=",Length(lBasis),
      " A_indecomposable_dimensions=",
      List(MTX.Indecomposition(aModule),pair->pair[2].dimension),
      " L_indecomposable_dimensions=",
      List(MTX.Indecomposition(lModule),pair->pair[2].dimension),"\n");
  marking:=label[2];
  if not IsBound(A4TwistInventory[marking]) then
    A4TwistInventory[marking]:=[tuple,Length(lBasis)];
    return;
  fi;
  individualLDimensions:=A4TwistInventory[marking][2]+Length(lBasis);
  combined:=List([1..4],index->A4DirectSumMatrix(
      A4TwistInventory[marking][1][index],tuple[index]));
  r:=combined[1]; y:=combined[2]; u:=combined[3]; b:=combined[4];
  t:=y^-1; s:=b*y; d:=s*t^-1;
  if Size(Group([r,u,d]))<>48 then Error("unexpected mixed L order"); fi;
  combinedA:=A4CentralizerAlgebraBasis([r,u]);
  combinedL:=A4CentralizerAlgebraBasis([r,u,d]);
  combinedQ:=A4CentralizerAlgebraBasis(combined);
  crossHomDimension:=Length(combinedL)-individualLDimensions;
  Print("MIXED_TWIST_INVENTORY marking=",marking,
      " combined_A_centralizer_dimension=",Length(combinedA),
      " L_order=48",
      " combined_L_centralizer_dimension=",Length(combinedL),
      " sum_individual_L_dimensions=",individualLDimensions,
      " L_cross_hom_dimension=",crossHomDimension,
      " combined_Q_centralizer_dimension=",Length(combinedQ),"\n");
  if IsBound(ANALYZE_MIXED_V4) and ANALYZE_MIXED_V4 then
    A4AnalyzeMixedV4(combined,["O8+",marking,"mixed"]);
  fi;
end;;

Reset(GlobalMersenneTwister,1);;
Reset(GlobalRandomSource,1);;
Read("experiments/atlas_a4_q1920_o8p_discovery.g");;
