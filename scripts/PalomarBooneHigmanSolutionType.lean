import Palomar.BooneHigmanSolution

/-!
# Dump the Boone–Higman megasubmission statements and their declaration closures (Solution side)

The twin of `scripts/PalomarBooneHigmanChallengeType.lean`, modeled on
`scripts/PalomarLIXStrongChallengeType.lean`. `Palomar/comparator-boone-higman.json` is
pending: the solution proves each selected statement from a proposition the development still
owes, under the name with `_of` appended. So the report is in two groups separated by
`pending-boundary:`. The shared block, printed first, is diffed against the twin and gates;
the compared statements, printed after the boundary, are reported without gating.

Run with `scripts/remote-build.sh --run scripts/PalomarBooneHigmanSolutionType.lean`.
-/

open Lean Meta in
#eval show MetaM Unit from do
  let targets : List (Bool × Name) :=
    [(true,  `BooneHigman.IsMetabelianGroup),
     (true,  `BooneHigman.EmbedsInFinitelyPresentedSimpleGroup),
     (true,  `BooneHigman.leavittResolventGenerator),
     (true,  `BooneHigman.leavittResolventRelation),
     (true,  `BooneHigman.LeavittResolventRing),
     (true,  `BooneHigman.steinbergRelations),
     (true,  `BooneHigman.SteinbergGroup),
     (true,  `BooneHigman.IsSelfSimilar),
     (true,  `BooneHigman.IsClassTransposition),
     (true,  `BooneHigman.classTranspositionGroup),
     (true,  `BooneHigman.IsResidueClassWiseAffine),
     (true,  `BooneHigman.mixedIdentities),
     (true,  `BooneHigman.IsSmoothModulus),
     (true,  `BooneHigman.IsClassTranspositionOver),
     (true,  `BooneHigman.classTranspositionGroupOver),
     (true,  `BooneHigman.IsClassShift),
     (true,  `BooneHigman.IsClassReflection),
     (false, `BooneHigman.explicit_fp_overgroup_of_all_gl_n_q_of),
     (false, `BooneHigman.finitely_presented_metabelian_embeds_in_finitely_presented_simple_of),
     (false, `BooneHigman.finitely_generated_metabelian_embeds_in_finitely_presented_simple_of),
     (false, `BooneHigman.finitely_generated_linear_embeds_in_finitely_presented_simple_of),
     (false, `BooneHigman.finitely_generated_linear_embeds_in_finitely_presented_self_similar_of),
     (false, `BooneHigman.kourovka_17_59_of),
     (false, `BooneHigman.kourovka_21_75_of),
     (false, `BooneHigman.kohl_factorization_conjecture_of),
     (false, `BooneHigman.exists_fp_simple_with_mixed_identities_not_finitely_normally_generated_of)]
  let env ← getEnv
  let mut boundaryPrinted := false
  for (isShared, target) in targets do
    unless isShared || boundaryPrinted do
      IO.println "pending-boundary:"
      boundaryPrinted := true
    let some info := env.find? target
      | throwError "declaration {target} is not in this environment"
    IO.println s!"declaration: {target}"
    IO.println s!"levelParams: {info.levelParams}"
    IO.println s!"typeHash: {hash info.type}"
    -- the transitive closure of constants the compared type mentions, which is
    -- exactly the set Comparator compares
    let mut seen : NameSet := {}
    let mut stack : List Name := info.type.getUsedConstants.toList
    while !stack.isEmpty do
      let n :: rest := stack | break
      stack := rest
      if seen.contains n then continue
      seen := seen.insert n
      if let some ci := env.find? n then
        stack := ci.type.getUsedConstants.toList ++ stack
        if let some v := ci.value? then
          stack := v.getUsedConstants.toList ++ stack
    let names := seen.toList.toArray.qsort (·.lt ·)
    IO.println s!"closure: {names.size}"
    for n in names do
      match env.find? n with
      | none => IO.println s!"  {n} MISSING"
      | some ci =>
          let v := match ci.value? with
            | some e => toString (hash e)
            | none => "none"
          IO.println s!"  {n} type={hash ci.type} value={v}"
    let fmt ← withOptions
      (fun o => (o.setBool `pp.all true).setBool `pp.explicit true) do
        ppExpr info.type
    IO.println "type:"
    IO.println (toString fmt)
  unless boundaryPrinted do
    throwError "no compared statement was reported, so the pending boundary was never printed"
