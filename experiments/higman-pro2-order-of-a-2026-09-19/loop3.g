# loop3.g: the class loop of loop2.g, checkpointed after every phase of a class (DefineNewGenerators,
# ComputeTails, EvaluateConsistency, lift/relations), so that one class may span several 1200 s runs.
# Resume with `gap -L NAME.ws loop3.g` (run4.sh).  No truncation: KEEP is ignored (full class-cl quotient).
if not IsBound(phase) then phase := 0; fi;
SAVE := function() SaveWorkspace(Concatenation(NAME, ".ws")); end;
while cl < MAXCL do
  if phase = 0 then
    tp := Runtime();
    if DefineNewGenerators(qs) = fail then Print(NAME, " collector too small\n"); break; fi;
    phase := 1; Print(NAME, " class ", cl+1, " phase define s ", Int((Runtime()-tp)/1000), "\n"); SAVE();
  fi;
  if phase = 1 then
    tp := Runtime(); ComputeTails(qs);
    phase := 2; Print(NAME, " class ", cl+1, " phase tails s ", Int((Runtime()-tp)/1000), "\n"); SAVE();
  fi;
  if phase = 2 then
    tp := Runtime(); EvaluateConsistency(qs);
    phase := 3; Print(NAME, " class ", cl+1, " phase consistency s ", Int((Runtime()-tp)/1000), "\n"); SAVE();
  fi;
  if phase = 3 then
    tp := Runtime(); LiftEpimorphism(qs);
    c := qs!.numberOfHighestWeightGenerators; M := CentralRelations(qs);
    R := List(M.bound, i -> M.matrix[i] * One(GF(2))); q := c - Length(R);
    tails := List([1..4], i -> TailOfPower(qs, i, ords[i])); dbl := [];
    for i in [1..4] do
      if Length(R) = 0 or RankMat(Concatenation(R, [tails[i]])) > Length(R) then Add(dbl, i); fi;
    od;
    for i in dbl do ords[i] := 2*ords[i]; od;
    IncorporateCentralRelations(qs);
    if qs!.numberOfHighestWeightGenerators > Length(qs!.eliminatedGens) then
      RenumberHighestWeightGenerators(qs);
    else
      Print(NAME, " finite: no new layer at class ", cl+1, "\n"); break;
    fi;
    cl := cl + 1; phase := 0;
    Print(NAME, " class ", cl, " layer ", q, " |P| = 2^", GeneratorNumberOfQuotient(qs), " ords ", ords,
          " lift s ", Int((Runtime()-tp)/1000), "\n");
    SAVE();
  fi;
od;
Print(NAME, " done class ", cl, " ords ", ords, "\n");
QUIT;
