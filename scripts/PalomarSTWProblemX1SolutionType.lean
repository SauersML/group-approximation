import Palomar.STWProblemX1Solution

/-!
# Dump the Problem X(1) statements and their declaration closures

The solution-side driver for `Palomar/comparator-stw-x1.json`, twin of
`scripts/PalomarSTWProblemX1ChallengeType.lean`.

`leanprover/comparator` compares the exported challenge and solution
`ConstantVal`s structurally and then walks the constants each compared type
mentions, transitively, requiring each to be identical in both environments:
name, type and value.  For the shared definitions, the constructors of the four
shared structures and the two compared theorems this driver prints the level
parameters, the type hash, the transitive closure with a type and value hash
per constant, and the `pp.all` type, and
`scripts/check_palomar_statement_match.sh` diffs the two drivers' output.

The constructors are listed because a structure's own type is a sort, so its
fields are reached only through `mk`.  The solution imports the development,
whose instances the challenge never sees, so this is where an instance resolved
differently inside a shared definition shows up.

Run with `lake env lean scripts/PalomarSTWProblemX1SolutionType.lean`.
-/

open Lean Meta in
#eval show MetaM Unit from do
  let targets : List (Bool × Name) :=
    [(true,  `STWProblemX1.FiniteCarrier.mk),
     (true,  `STWProblemX1.finiteCarrierCoeSort),
     (true,  `STWProblemX1.finiteCarrierFintype),
     (true,  `STWProblemX1.finiteCarrierDecidableEq),
     (true,  `STWProblemX1.normalizedTrace),
     (true,  `STWProblemX1.hilbertSchmidtNorm),
     (true,  `STWProblemX1.IsCompletelyPositive),
     (true,  `STWProblemX1.TracialState.mk),
     (true,  `STWProblemX1.AmenableTraceModel.mk),
     (true,  `STWProblemX1.QuasidiagonalTraceModel.mk),
     (true,  `STWProblemX1.IsAmenableTrace),
     (true,  `STWProblemX1.IsQuasidiagonalTrace),
     (false, `STWProblemX1.exists_separable_amenable_not_quasidiagonal),
     (false, `STWProblemX1.not_every_amenable_trace_quasidiagonal)]
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
