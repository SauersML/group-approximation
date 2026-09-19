# Reusable exact all-multiplicity collision analyzer for a marked F2-module.
# Load this file before a module-construction script.  That script can then call
# AnalyzeRepeatedCollisionModule([r,y,u,b],label).

if LoadPackage("GBNP")<>true then Error("GBNP is required"); fi;
SetInfoLevel(InfoGBNP,0);

A4MatrixFromCoordinates:=function(coordinates,basis)
  local result,index;
  result:=Zero(basis[1]);
  for index in [1..Length(basis)] do
    result:=result+coordinates[index]*basis[index];
  od;
  return ImmutableMatrix(GF(2),result);
end;;

A4CentralizerAlgebraBasis:=function(generators)
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
      A4MatrixFromCoordinates(coordinates,matrixBasis));
end;;

A4Submatrix:=function(current,rowIndices,columnIndices)
  return ImmutableMatrix(GF(2),List(rowIndices,i->
      List(columnIndices,j->current[i][j])));
end;;

# The dimension-20 orthogonal slices restrict to A as 1^4+U^2, with U the
# absolutely irreducible two-dimensional S3 module.  Put this decomposition
# in matrix-unit coordinates M4(F2) x M2(F2), which is much sparser than an
# arbitrary nullspace basis of the same centralizer algebra.
A4SemisimpleAIsotypicCoordinates:=function(tuple,aIndecomposition)
  local oneComponents,twoComponents,change,changed,aGenerators,firstBlocks,
        secondBlocks,aligner,alignmentRows,i,j,alignedChange,aligned,basis,
        current,rowBlock,columnBlock,expectedDimensions;
  expectedDimensions:=SortedList(List(aIndecomposition,
      pair->pair[2].dimension));
  if expectedDimensions<>[1,1,1,1,2,2] then
    Error("A-isotypic coordinates require restriction 1^4+U^2");
  fi;
  oneComponents:=Filtered(aIndecomposition,pair->pair[2].dimension=1);
  twoComponents:=Filtered(aIndecomposition,pair->pair[2].dimension=2);
  change:=ImmutableMatrix(GF(2),Concatenation(List(
      Concatenation(oneComponents,twoComponents),pair->pair[1])));
  if RankMat(change)<>8 then Error("A-indecomposition basis is singular"); fi;
  changed:=List(tuple,generator->change*generator*change^-1);
  aGenerators:=[changed[1],changed[3]];
  firstBlocks:=List(aGenerators,current->A4Submatrix(current,[5,6],[5,6]));
  secondBlocks:=List(aGenerators,current->A4Submatrix(current,[7,8],[7,8]));
  aligner:=First(Elements(GL(2,2)),candidate->
      ForAll([1,2],index->candidate*secondBlocks[index]*candidate^-1=
          firstBlocks[index]));
  if aligner=fail then Error("the two simple A blocks did not align"); fi;
  alignmentRows:=IdentityMat(8,GF(2));
  for i in [1,2] do
    for j in [1,2] do
      alignmentRows[i+6][j+6]:=aligner[i][j];
    od;
  od;
  alignedChange:=ImmutableMatrix(GF(2),alignmentRows)*change;
  aligned:=List(tuple,generator->alignedChange*generator*alignedChange^-1);
  basis:=[];
  for i in [1..4] do
    for j in [1..4] do
      current:=NullMat(8,8,GF(2));
      current[i][j]:=One(GF(2));
      Add(basis,ImmutableMatrix(GF(2),current));
    od;
  od;
  for rowBlock in [0,1] do
    for columnBlock in [0,1] do
      current:=NullMat(8,8,GF(2));
      current[5+2*rowBlock][5+2*columnBlock]:=One(GF(2));
      current[6+2*rowBlock][6+2*columnBlock]:=One(GF(2));
      Add(basis,ImmutableMatrix(GF(2),current));
    od;
  od;
  if not ForAll(basis,current->current*aligned[1]=aligned[1]*current and
      current*aligned[3]=aligned[3]*current) then
    Error("matrix-unit basis does not centralize A");
  fi;
  return [aligned,basis,alignedChange];
end;;

AnalyzeRepeatedCollisionModule:=function(tuple,label)
  local r,y,u,b,t,s,n,basis,basisSize,names,freeAlgebra,freeGenerators,
        freeOne,variables,liftScalarMatrix,genericC,freeT,freeS,freeIdentity,
        baseMatrices,baseRelations,baseGb,collisionMatrix,
        collisionRelations,reducedCollision,fullGb,identityCoordinates,
        targetNormalForms,identityForced,coordinateSpace,coordinates,current,
        collisionWord,oneBlockSolutions,nonidentitySolutions,faithfulSolutions,
        coordinateIterator,qModule,aModule,kModule,qIndecomposition,
        aIndecomposition,kIndecomposition,qCompositionFactors,isotypicData,
        fullRelations,fullNpRelations,
        linearNpRelations,linearGb,homogenizingVariable,homogenizingIndex,
        homogenizeNp,homogeneousRelations,commutatorRelations,truncationDegree,
        truncatedGb,truncatedTargets,truncatedNormalForms,polynomialDegree;
  r:=tuple[1]; y:=tuple[2]; u:=tuple[3]; b:=tuple[4];
  t:=y^-1; s:=b*y; n:=Length(r);
  qModule:=GModuleByMats(tuple,GF(2));
  aModule:=GModuleByMats([r,u],GF(2));
  kModule:=GModuleByMats([t,s],GF(2));
  qIndecomposition:=MTX.Indecomposition(qModule);
  aIndecomposition:=MTX.Indecomposition(aModule);
  kIndecomposition:=MTX.Indecomposition(kModule);
  qCompositionFactors:=MTX.CompositionFactors(qModule);
  Print("REPEATED_MODULE label=",label,
      " Q_indecomposable_dimensions=",
      List(qIndecomposition,pair->pair[2].dimension),
      " A_indecomposable_dimensions=",
      List(aIndecomposition,pair->pair[2].dimension),
      " K_indecomposable_dimensions=",
      List(kIndecomposition,pair->pair[2].dimension),
      " Q_composition_dimensions=",
      List(qCompositionFactors,factor->factor.dimension),"\n");
  if IsBound(EXPORT_REPEATED_DECOMPOSITION) and
     EXPORT_REPEATED_DECOMPOSITION then
    Print("REPEATED_A_INDECOMPOSITION label=",label," data=",
        aIndecomposition,"\n");
  fi;
  basis:=A4CentralizerAlgebraBasis([r,u]);
  basisSize:=Length(basis);
  if IsBound(REPEATED_USE_A_ISOTYPIC) and REPEATED_USE_A_ISOTYPIC then
    if basisSize<>20 then
      Print("REPEATED_ISOTYPIC_SKIP label=",label,
          " centralizer_dimension=",basisSize,"\n");
      return rec(label:=label,moduleDimension:=n,
          centralizerDimension:=basisSize,skipped:=true);
    fi;
    isotypicData:=A4SemisimpleAIsotypicCoordinates(tuple,aIndecomposition);
    tuple:=isotypicData[1];
    basis:=isotypicData[2];
    r:=tuple[1]; y:=tuple[2]; u:=tuple[3]; b:=tuple[4];
    t:=y^-1; s:=b*y;
    if Length(basis)<>basisSize then
      Error("isotypic centralizer dimension changed");
    fi;
    Print("REPEATED_ISOTYPIC label=",label,
        " centralizer_structure=M4(F2)xM2(F2)\n");
    if IsBound(EXPORT_REPEATED_ISOTYPIC_MATRICES) and
       EXPORT_REPEATED_ISOTYPIC_MATRICES then
      Print("REPEATED_ISOTYPIC_MATRICES label=",label," tuple=",
          List(tuple,current->List(current,row->List(row,IntFFE))),"\n");
    fi;
  fi;
  if IsBound(REPEATED_ENUMERATE_ONE_BLOCK) and
     REPEATED_ENUMERATE_ONE_BLOCK then
    coordinateSpace:=VectorSpace(GF(2),IdentityMat(basisSize,GF(2)));
    coordinateIterator:=Iterator(coordinateSpace);
    oneBlockSolutions:=[];
    faithfulSolutions:=[];
    while not IsDoneIterator(coordinateIterator) do
      coordinates:=NextIterator(coordinateIterator);
      current:=A4MatrixFromCoordinates(coordinates,basis);
      if IsOne(current^2) and IsOne((current*t)^3) then
        collisionWord:=t*current*s*current*t^-1*current*s*t*current;
        if IsOne(collisionWord) then
          Add(oneBlockSolutions,[coordinates,current]);
          if Size(Group([t,s,current]))=24 and
             StructureDescription(Group([t,s,current]))="S4" then
            Add(faithfulSolutions,[coordinates,current]);
          fi;
        fi;
      fi;
    od;
    nonidentitySolutions:=Filtered(oneBlockSolutions,pair->
        not IsOne(pair[2]));
    Print("REPEATED_ONE_BLOCK label=",label,
        " centralizer_dimension=",basisSize,
        " solution_count=",Length(oneBlockSolutions),
        " nonidentity_count=",Length(nonidentitySolutions),
        " faithful_s4_count=",Length(faithfulSolutions),"\n");
    if Length(nonidentitySolutions)>0 then
      Print("REPEATED_ONE_BLOCK_FIRST_NONIDENTITY label=",label,
          " coordinates=",List(nonidentitySolutions[1][1],IntFFE),
          " matrix=",List(nonidentitySolutions[1][2],row->List(row,IntFFE)),
          " generated_order=",Size(Group([t,s,nonidentitySolutions[1][2]])),
          " generated_structure=",
          StructureDescription(Group([t,s,nonidentitySolutions[1][2]])),"\n");
    fi;
  fi;
  if IsBound(REPEATED_CENTRALIZER_DIMENSION) and
     basisSize<>REPEATED_CENTRALIZER_DIMENSION then
    Print("REPEATED_SKIP label=",label," module_dimension=",n,
        " centralizer_dimension=",basisSize,"\n");
    return rec(label:=label,moduleDimension:=n,
        centralizerDimension:=basisSize,skipped:=true);
  fi;
  names:=List([0..basisSize-1],index->Concatenation("x",String(index)));
  if IsBound(REPEATED_HOMOGENIZED_TRUNCATION_DEGREE) then
    Add(names,"h");
  fi;
  freeAlgebra:=CallFuncList(FreeAssociativeAlgebraWithOne,
      Concatenation([GF(2)],names));
  freeGenerators:=GeneratorsOfAlgebra(freeAlgebra);
  freeOne:=freeGenerators[1];
  variables:=freeGenerators{[2..basisSize+1]};
  if IsBound(REPEATED_HOMOGENIZED_TRUNCATION_DEGREE) then
    homogenizingVariable:=freeGenerators[basisSize+2];
    homogenizingIndex:=basisSize+1;
  fi;
  liftScalarMatrix:=function(current)
    return List(current,row->List(row,entry->IntFFE(entry)*freeOne));
  end;
  genericC:=List([1..n],i->List([1..n],j->
      Sum([1..basisSize],k->IntFFE(basis[k][i][j])*variables[k])));
  freeT:=liftScalarMatrix(t);
  freeS:=liftScalarMatrix(s);
  freeIdentity:=liftScalarMatrix(IdentityMat(n,GF(2)));
  if IsBound(REPEATED_USE_V4_PRESENTATION) and
     REPEATED_USE_V4_PRESENTATION then
    # The marked local presentation is universally S4.  Its normal V4 can be
    # presented over K=<t,s> by c^s=c^t and c*c^t=c^(t^2).  These replace the
    # original cubic/quartic relators by linear/quadratic matrix equations.
    baseMatrices:=[genericC*genericC+freeIdentity,
      freeS*genericC*freeS+(freeT^2)*genericC*freeT,
      genericC*(freeT^2)*genericC*freeT+
          freeT*genericC*(freeT^2)];
    baseRelations:=Filtered(Set(Concatenation(List(baseMatrices,
        current->Concatenation(current)))),entry->not IsZero(entry));
    Print("REPEATED_V4_BASE label=",label,
        " module_dimension=",n,
        " centralizer_dimension=",basisSize,
        " relation_count=",Length(baseRelations),"\n");
    fullGb:=SGrobner(GP2NPList(baseRelations));
    identityCoordinates:=SolutionMat(List(basis,current->Flat(current)),
        Flat(IdentityMat(n,GF(2))));
    targetNormalForms:=List([1..basisSize],index->StrongNormalFormNP(
        GP2NP(variables[index]+IntFFE(identityCoordinates[index])*freeOne),
        fullGb));
    identityForced:=ForAll(targetNormalForms,current->current=[[],[]]);
    Print("REPEATED_V4_RESULT label=",label,
        " gb_count=",Length(fullGb),
        " identity_coordinates=",List(identityCoordinates,IntFFE),
        " identity_forced=",identityForced,"\n");
    if IsBound(EXPORT_REPEATED_NC_GB) and EXPORT_REPEATED_NC_GB then
      CallFuncList(GBNP.ConfigPrint,names);
      Print("REPEATED_V4_CERTIFICATE label=",label,"\n");
      Print("full_groebner_basis=\n");
      PrintNPList(fullGb);
      Print("identity_normal_forms=\n");
      PrintNPList(targetNormalForms);
    fi;
    return rec(label:=label,moduleDimension:=n,
        centralizerDimension:=basisSize,
        relationCount:=Length(baseRelations),fullGb:=fullGb,
        identityCoordinates:=identityCoordinates,
        identityForced:=identityForced);
  fi;
  baseMatrices:=[genericC*genericC+freeIdentity,
                (genericC*freeT)^3+freeIdentity];
  baseRelations:=Filtered(Set(Concatenation(List(baseMatrices,
      current->Concatenation(current)))),entry->not IsZero(entry));
  Print("REPEATED_BASE label=",label," module_dimension=",n,
      " centralizer_dimension=",basisSize,
      " base_relation_count=",Length(baseRelations),"\n");
  if IsBound(REPEATED_COLLISION_STOP_BEFORE_GB) and
     REPEATED_COLLISION_STOP_BEFORE_GB then
    return rec(label:=label,moduleDimension:=n,
        centralizerDimension:=basisSize,
        baseRelationCount:=Length(baseRelations));
  fi;
  collisionMatrix:=
      freeT*genericC*freeS*genericC*(freeT^2)*genericC*freeS*freeT*genericC+
          freeIdentity;
  collisionRelations:=Filtered(Set(Concatenation(collisionMatrix)),
      entry->not IsZero(entry));
  if IsBound(REPEATED_HOMOGENIZED_TRUNCATION_DEGREE) then
    truncationDegree:=REPEATED_HOMOGENIZED_TRUNCATION_DEGREE;
    fullRelations:=Set(Concatenation(baseRelations,collisionRelations));
    fullNpRelations:=GP2NPList(fullRelations);
    homogenizeNp:=function(np)
      local degree,words;
      degree:=Maximum(List(np[1],Length));
      words:=List(np[1],word->Concatenation(word,
          ListWithIdenticalEntries(degree-Length(word),homogenizingIndex)));
      return GP2NP(NP2GP([words,np[2]],freeAlgebra));
    end;
    homogeneousRelations:=List(fullNpRelations,homogenizeNp);
    commutatorRelations:=List(variables,variable->GP2NP(
        homogenizingVariable*variable+variable*homogenizingVariable));
    homogeneousRelations:=Concatenation(homogeneousRelations,
        commutatorRelations);
    polynomialDegree:=CheckHomogeneousNPs(homogeneousRelations,
        ListWithIdenticalEntries(basisSize+1,1));
    if polynomialDegree=false then Error("homogenization failed"); fi;
    truncatedGb:=SGrobnerTrunc(homogeneousRelations,truncationDegree,
        ListWithIdenticalEntries(basisSize+1,1));
    identityCoordinates:=SolutionMat(List(basis,current->Flat(current)),
        Flat(IdentityMat(n,GF(2))));
    truncatedTargets:=List([1..basisSize],index->
        homogenizingVariable^(truncationDegree-1)*
        (variables[index]+IntFFE(identityCoordinates[index])*
            homogenizingVariable));
    truncatedNormalForms:=List(truncatedTargets,target->
        StrongNormalFormNP(GP2NP(target),truncatedGb));
    Print("REPEATED_HOMOGENIZED_TRUNCATION label=",label,
        " degree=",truncationDegree,
        " input_degree_histogram=",Collected(polynomialDegree),
        " gb_count=",Length(truncatedGb),
        " identity_homogenizations_forced=",
        ForAll(truncatedNormalForms,current->current=[[],[]]),"\n");
    if IsBound(EXPORT_REPEATED_TRUNCATED_GB) and
       EXPORT_REPEATED_TRUNCATED_GB then
      CallFuncList(GBNP.ConfigPrint,names);
      Print("truncated_identity_normal_forms=\n");
      PrintNPList(truncatedNormalForms);
    fi;
    return rec(label:=label,moduleDimension:=n,
        centralizerDimension:=basisSize,truncationDegree:=truncationDegree,
        truncatedGb:=truncatedGb,
        identityHomogenizationsForced:=ForAll(truncatedNormalForms,
            current->current=[[],[]]));
  fi;
  if IsBound(REPEATED_RAW_LINEAR_AUDIT) and REPEATED_RAW_LINEAR_AUDIT then
    fullRelations:=Set(Concatenation(baseRelations,collisionRelations));
    fullNpRelations:=GP2NPList(fullRelations);
    linearNpRelations:=Filtered(fullNpRelations,np->
        ForAll(np[1],word->Length(word)<=1));
    linearGb:=SGrobner(linearNpRelations);
    identityCoordinates:=SolutionMat(List(basis,current->Flat(current)),
        Flat(IdentityMat(n,GF(2))));
    targetNormalForms:=List([1..basisSize],index->StrongNormalFormNP(
        GP2NP(variables[index]+IntFFE(identityCoordinates[index])*freeOne),
        linearGb));
    Print("REPEATED_RAW_LINEAR label=",label,
        " degree_histogram=",Collected(List(fullNpRelations,np->
            Maximum(List(np[1],Length)))),
        " linear_relation_count=",Length(linearNpRelations),
        " linear_gb_count=",Length(linearGb),
        " identity_forced=",
        ForAll(targetNormalForms,current->current=[[],[]]),"\n");
    if IsBound(REPEATED_RAW_LINEAR_STOP) and REPEATED_RAW_LINEAR_STOP then
      return rec(label:=label,moduleDimension:=n,
          centralizerDimension:=basisSize,linearGb:=linearGb,
          identityCoordinates:=identityCoordinates,
          identityNormalForms:=targetNormalForms);
    fi;
  fi;
  if IsBound(REPEATED_DIRECT_FULL_GB) and REPEATED_DIRECT_FULL_GB then
    fullGb:=SGrobner(GP2NPList(Set(Concatenation(baseRelations,
        collisionRelations))));
    identityCoordinates:=SolutionMat(List(basis,current->Flat(current)),
        Flat(IdentityMat(n,GF(2))));
    targetNormalForms:=List([1..basisSize],index->StrongNormalFormNP(
        GP2NP(variables[index]+IntFFE(identityCoordinates[index])*freeOne),
        fullGb));
    identityForced:=ForAll(targetNormalForms,current->current=[[],[]]);
    Print("REPEATED_DIRECT_RESULT label=",label,
        " module_dimension=",n,
        " centralizer_dimension=",basisSize,
        " full_relation_count=",Length(Set(Concatenation(baseRelations,
            collisionRelations))),
        " full_gb_count=",Length(fullGb),
        " identity_coordinates=",List(identityCoordinates,IntFFE),
        " identity_forced=",identityForced,"\n");
    if IsBound(EXPORT_REPEATED_NC_GB) and EXPORT_REPEATED_NC_GB then
      CallFuncList(GBNP.ConfigPrint,names);
      Print("REPEATED_DIRECT_CERTIFICATE label=",label,"\n");
      Print("full_groebner_basis=\n");
      PrintNPList(fullGb);
      Print("identity_normal_forms=\n");
      PrintNPList(targetNormalForms);
    fi;
    return rec(label:=label,moduleDimension:=n,
        centralizerDimension:=basisSize,
        baseRelationCount:=Length(baseRelations),fullGb:=fullGb,
        identityCoordinates:=identityCoordinates,
        identityForced:=identityForced);
  fi;
  baseGb:=SGrobner(GP2NPList(baseRelations));
  reducedCollision:=Set(List(GP2NPList(collisionRelations),current->
      StrongNormalFormNP(current,baseGb)));
  reducedCollision:=Filtered(reducedCollision,current->current<>[[],[]]);
  fullGb:=SGrobner(Concatenation(baseGb,reducedCollision));
  identityCoordinates:=SolutionMat(List(basis,current->Flat(current)),
      Flat(IdentityMat(n,GF(2))));
  targetNormalForms:=List([1..basisSize],index->StrongNormalFormNP(
      GP2NP(variables[index]+IntFFE(identityCoordinates[index])*freeOne),
      fullGb));
  identityForced:=ForAll(targetNormalForms,current->current=[[],[]]);
  Print("REPEATED_RESULT label=",label,
      " module_dimension=",n,
      " centralizer_dimension=",basisSize,
      " base_relation_count=",Length(baseRelations),
      " base_gb_count=",Length(baseGb),
      " reduced_collision_count=",Length(reducedCollision),
      " full_gb_count=",Length(fullGb),
      " identity_coordinates=",List(identityCoordinates,IntFFE),
      " identity_forced=",identityForced,"\n");
  if IsBound(EXPORT_REPEATED_NC_GB) and EXPORT_REPEATED_NC_GB then
    CallFuncList(GBNP.ConfigPrint,names);
    Print("REPEATED_CERTIFICATE label=",label,"\n");
    Print("base_groebner_basis=\n");
    PrintNPList(baseGb);
    Print("collision_remainders_mod_base=\n");
    PrintNPList(reducedCollision);
    Print("full_groebner_basis=\n");
    PrintNPList(fullGb);
    Print("identity_normal_forms=\n");
    PrintNPList(targetNormalForms);
  fi;
  return rec(label:=label,moduleDimension:=n,
      centralizerDimension:=basisSize,
      baseRelationCount:=Length(baseRelations),baseGb:=baseGb,
      reducedCollision:=reducedCollision,fullGb:=fullGb,
      identityCoordinates:=identityCoordinates,
      identityForced:=identityForced);
end;;
