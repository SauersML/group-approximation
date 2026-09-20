# One exact p-quotient step, copied in order from GAP 4.15.1 PQuotient.
# Restore a workspace produced by pquotient.g before reading this file.
if not IsBound(HRF_STAGE) then HRF_STAGE:="all";fi;
if not HRF_STAGE in ["all","prepare","lift","finish"] then Error("unknown checkpoint stage");fi;
Print("ADVANCE from=",LengthOfDescendingSeries(pq)," target=",HRF_CLASS," stage=",HRF_STAGE,"\n");
if HRF_STAGE="prepare" or HRF_STAGE="all" then
  if IsBound(HRF_PENDING_CLASS) and HRF_PENDING_CLASS=HRF_CLASS
     and IsBound(HRF_PENDING_PHASE) and HRF_PENDING_PHASE in ["lift","relations"] then
    Error("layer already partly prepared; resume its pending phase");
  fi;
  if LengthOfDescendingSeries(pq)+1<>HRF_CLASS then Error("not a single next step");fi;
  Print("PHASE define generators\n");
  if DefineNewGenerators(pq)=fail then Error("collector capacity exceeded");fi;
  Print("PHASE compute tails\n");ComputeTails(pq);
  Print("PHASE consistency\n");EvaluateConsistency(pq);
  HRF_PENDING_CLASS:=HRF_CLASS;HRF_PENDING_PHASE:="lift";
  if HRF_STAGE="prepare" then
    SaveWorkspace(HRF_SAVE);Print("CHECKPOINT before lift epimorphism\n");QuitGap(0);
  fi;
fi;
if HRF_STAGE="lift" or HRF_STAGE="all" then
  if HRF_PENDING_CLASS<>HRF_CLASS or HRF_PENDING_PHASE<>"lift" then Error("wrong lift checkpoint");fi;
  Print("PHASE lift epimorphism\n");
  if HRF_STAGE="all" then
    LiftEpimorphism(pq);
  else
    # Exactly the core LiftEpimorphism/EvaluateRelators loop, with a
    # workspace after every fully collected relation and bounded batches.
    if not IsBound(HRF_LIFT_CLASS) or HRF_LIFT_CLASS<>HRF_CLASS then
      Print("PHASE inverse tails\n");TailsInverses(pq);
      HRF_LIFT_CLASS:=HRF_CLASS;HRF_RELATOR_INDEX:=1;
    fi;
    HRF_LIFT_STARTED:=Runtime();
    HRF_N:=GeneratorNumberOfQuotient(pq);;
    HRF_C:=pq!.numberOfHighestWeightGenerators;;
    HRF_FGENS:=GeneratorsOfGroup(FreeGroupOfFpGroup(pq!.preimage));;
    HRF_RELS:=RelatorsOfFpGroup(pq!.preimage);;
    while HRF_RELATOR_INDEX<=Length(HRF_RELS) do
      HRF_VECTOR:=ListWithIdenticalEntries(HRF_N+HRF_C,0);;
      HRF_WORD:=MappedWord(HRF_RELS[HRF_RELATOR_INDEX],HRF_FGENS,pq!.images);;
      Print("RELATOR ",HRF_RELATOR_INDEX," of ",Length(HRF_RELS),"\n");
      while CollectWordOrFail(pq!.collector,HRF_VECTOR,HRF_WORD)=fail do od;
      if not ForAll(HRF_VECTOR{[1..HRF_N]},x->x=0) then Error("source relator has noncentral lower coordinates");fi;
      AddVectorLTM(CentralRelations(pq),HRF_VECTOR{[HRF_N+1..HRF_N+HRF_C]});
      HRF_RELATOR_INDEX:=HRF_RELATOR_INDEX+1;
      SaveWorkspace(HRF_SAVE);
      if Runtime()-HRF_LIFT_STARTED>=20000 and HRF_RELATOR_INDEX<=Length(HRF_RELS) then
        Print("CHECKPOINT next relator ",HRF_RELATOR_INDEX,"\n");QuitGap(0);
      fi;
    od;
  fi;
  HRF_PENDING_PHASE:="relations";
  if HRF_STAGE="lift" then
    SaveWorkspace(HRF_SAVE);Print("CHECKPOINT before source relations\n");QuitGap(0);
  fi;
fi;
if HRF_PENDING_CLASS<>HRF_CLASS or HRF_PENDING_PHASE<>"relations" then Error("wrong relations checkpoint");fi;
Print("PHASE source relations\n");IncorporateCentralRelations(pq);
if pq!.numberOfHighestWeightGenerators>Length(pq!.eliminatedGens) then
  RenumberHighestWeightGenerators(pq);
  if LengthOfDescendingSeries(pq)<>HRF_CLASS then Error("unexpected completed p-class");fi;
else
  pq!.numberOfHighestWeightGenerators:=0;pq!.eliminatedGens:=[];
fi;
epi:=EpimorphismQuotientSystem(pq);;Q:=Image(epi);;
zimage:=Image(epi,z);;imgs:=List(bcgens,g->Image(epi,g));;
centralok:=ForAll(GeneratorsOfGroup(Q),g->Comm(g,zimage)=One(Q));;
presentationok:=ForAll(rels,r->MappedWord(r,fg,imgs)=One(Q));;
if not centralok or not presentationok then Error("verification failed");fi;
Print("RESULT class=",HRF_CLASS," log7order=",LogInt(Size(Q),7),
      " central_order=",Order(zimage),"\n");
Print("CENTRAL_CHECK ",centralok,"\nPRESENTATION_CHECK ",presentationok,"\n");
if IsBound(HRF_RESULT) then
  PrintTo(HRF_RESULT,"{\"prime\":7,\"p_class\":",LengthOfDescendingSeries(pq),
    ",\"log7_order\":",LogInt(Size(Q),7),",\"central_order\":",Order(zimage),
    ",\"layers\":",RanksOfDescendingSeries(pq),",\"source_relators_checked\":24}\n");
fi;
HRF_PENDING_PHASE:="complete";
if IsBound(HRF_SAVE) then SaveWorkspace(HRF_SAVE);fi;
QUIT;
