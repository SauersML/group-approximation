import Palomar.BowenChapmanSolution

/-!
# Dump the Bowen–Chapman statements and their declaration closures

The solution-side driver for `Palomar/comparator-bowen-chapman.json`, twin of
`scripts/PalomarBowenChapmanChallengeType.lean`, on the model of
`scripts/PalomarLIXStrongSolutionType.lean`.

`leanprover/comparator` compares the exported challenge and solution
`ConstantVal`s structurally and then walks the constants each compared type
mentions, transitively, requiring each to be identical in both environments:
name, type and value.

## Why this driver prints two groups

The configuration is pending: this side declares each selected statement as
`<theorem>_of`, with the development endpoint's statement as a hypothesis.
Everything before `pending-boundary:` is the shared block and is diffed against
the challenge twin, which gates; everything after it is printed for inspection.
When the endpoint lands, the names below lose their `_of`, the boundary moves to
the end, and the whole report is diffed.

Run with `scripts/remote-build.sh --run scripts/PalomarBowenChapmanSolutionType.lean`.
-/

open Lean Meta in
#eval show MetaM Unit from do
  let targets : List (Bool × Name) :=
    [(true,  `BowenChapman.cellularAutomaton),
     (true,  `BowenChapman.IsSurjunctive),
     (true,  `BowenChapman.hammingDist),
     (true,  `BowenChapman.IsSoficGroup),
     (false, `BowenChapman.not_all_surjunctive_groups_sofic_of),
     (false, `BowenChapman.exists_finitelyGenerated_surjunctive_not_sofic_of)]
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
  unless boundaryPrinted do
    throwError "no compared statement was reported, so the pending boundary was never printed"
