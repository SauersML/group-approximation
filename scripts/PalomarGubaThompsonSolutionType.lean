import Palomar.GubaThompsonSolution

/-!
# Dump the Guba Question 3.20 statements and their declaration closures

The solution-side driver for `Palomar/comparator-guba-thompson.json`, twin of
`scripts/PalomarGubaThompsonChallengeType.lean`.

`leanprover/comparator` compares the exported challenge and solution
`ConstantVal`s structurally and then walks the constants each compared type
mentions, transitively, requiring each to be identical in both environments:
name, type and value.  For the five shared definitions and the two compared
theorems this driver prints the level parameters, the type hash, the transitive
closure with a type and value hash per constant, and the `pp.all` type, and
`scripts/check_palomar_statement_match.sh` diffs the two drivers' output.

The solution imports the development, whose instances the challenge never sees,
so this is where an instance resolved differently inside a shared definition
shows up.

Run with `lake env lean scripts/PalomarGubaThompsonSolutionType.lean`.
-/

open Lean Meta in
#eval show MetaM Unit from do
  let targets : List (Bool × Name) :=
    [(true,  `GubaThompson.conjBy),
     (true,  `GubaThompson.thompsonRels),
     (true,  `GubaThompson.ThompsonF),
     (true,  `GubaThompson.x0),
     (true,  `GubaThompson.x1),
     (false, `GubaThompson.question_3_20),
     (false, `GubaThompson.question_3_20_common_multiple)]
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
