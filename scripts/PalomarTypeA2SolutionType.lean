import Palomar.TypeA2Solution

/-!
# Dump the FFWZ Question 5.8 statement and its declaration closure

The solution-side driver for `Palomar/comparator-type-a2.json`, twin of
`scripts/PalomarTypeA2ChallengeType.lean`.

`leanprover/comparator` decides a submission by comparing the exported
Challenge and Solution `ConstantVal`s structurally -- not up to definitional
unfolding -- and then walking the constants each compared type mentions,
transitively, requiring each ordinary declaration to be IDENTICAL in both
environments.  Identical means name, type **and value**.

## Why this driver prints two groups

The configuration is not submittable yet: `Palomar/TypeA2Solution.lean` derives
the selected statement from `GroupApproximation.TypeA2.Question58`, which the
development does not prove yet, so its theorem carries a hypothesis the
challenge's does not and is named `<theorem>_of`.  Comparing the two sides'
theorem statements today would report a difference that is the honest state of
the work.

What can be compared today is the **shared block**: `IsTypeA2` and
`actionKernel`, written byte-identically in both files.  The solution imports
the development, whose instances the challenge never sees, so an instance
resolved differently inside one of them shows up here and fails the real
Comparator.

So the report is in two groups, separated by `pending-boundary:`.  Everything
before the boundary is diffed against the Challenge twin and gates;
everything after it is printed for inspection.  The name after the boundary
carries the `_of` suffix on this side, because that is what the solution
declares while the proposition is outstanding.  When it is proved, the theorem
name below loses its `_of`, the boundary moves to the end, and the whole report
is diffed like the submittable pairs.

Run with `lake env lean scripts/PalomarTypeA2SolutionType.lean`.
-/

open Lean Meta in
#eval show MetaM Unit from do
  -- `(true, n)` is a shared-block declaration, printed before the boundary and
  -- diffed against the twin; `(false, n)` is a compared statement, printed
  -- after it and reported without gating.  One flat list and one inline body,
  -- matching `scripts/PalomarLIXStrongSolutionType.lean` exactly, so that the
  -- drivers cannot drift in how they walk the closure.
  let targets : List (Bool × Name) :=
    [(true,  `FFWZ.IsTypeA2),
     (true,  `FFWZ.actionKernel),
     (false, `FFWZ.exists_isTypeA2_quotient_not_isFinitelyPresented_of)]
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
