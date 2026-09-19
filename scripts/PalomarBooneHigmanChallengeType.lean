import Palomar.BooneHigmanChallenge

/-!
# Dump the Boone–Higman stage 1 statements and their declaration closures (Challenge side)

The challenge-side driver for `Palomar/comparator-boone-higman.json`, twin of
`scripts/PalomarBooneHigmanSolutionType.lean` and modeled on
`scripts/PalomarBlanchardToeplitzChallengeType.lean`.

`leanprover/comparator` compares the exported challenge and solution `ConstantVal`s
structurally, then walks the constants each compared type mentions, transitively, requiring
each to be identical in both environments. For the definitions of the shared block and each
compared theorem, this driver prints the level parameters, the type hash, the transitive
closure with a type and value hash per constant, and the `pp.all` type. Diff the two drivers'
output. The values of the shared definitions are walked; the proofs of the theorems are not.

Run with `lake env lean scripts/PalomarBooneHigmanChallengeType.lean`.
-/

open Lean Meta in
#eval show MetaM Unit from do
  let targets : List (Bool × Name) :=
    [(true,  `BooneHigman.leavittResolventGenerator),
     (true,  `BooneHigman.leavittResolventRelation),
     (true,  `BooneHigman.LeavittResolventRing),
     (true,  `BooneHigman.steinbergRelations),
     (true,  `BooneHigman.SteinbergGroup),
     (true,  `BooneHigman.IsClassTransposition),
     (true,  `BooneHigman.classTranspositionGroup),
     (true,  `BooneHigman.IsResidueClassWiseAffine),
     (true,  `BooneHigman.IsClassShift),
     (true,  `BooneHigman.IsClassReflection),
     (false, `BooneHigman.explicit_fp_overgroup_of_all_gl_n_q),
     (false, `BooneHigman.kourovka_17_59),
     (false, `BooneHigman.kohl_factorization_conjecture)]
  let env ← getEnv
  for (isShared, target) in targets do
    let some info := env.find? target
      | throwError "declaration {target} is not in this environment"
    IO.println s!"declaration: {target}"
    IO.println s!"levelParams: {info.levelParams}"
    IO.println s!"typeHash: {hash info.type}"
    let mut seen : NameSet := {}
    let mut stack : List Name := info.type.getUsedConstants.toList
    if let some v := info.value? then
      if isShared then
        stack := v.getUsedConstants.toList ++ stack
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
