import Palomar.LIXStrongChallenge

/-!
# Dump the strengthened LIX statements and their declaration closures

The twin of `scripts/PalomarLIXChallengeType.lean` for the third Comparator
configuration, `Palomar/comparator-lix-strong.json`, and it differs from that
twin in one way that is the whole point of it.

`leanprover/comparator` decides a submission by comparing the exported
Challenge and Solution `ConstantVal`s structurally -- not up to definitional
unfolding -- and then walking the constants each compared type mentions,
transitively, requiring each ordinary declaration to be IDENTICAL in both
environments.  Identical means name, type **and value**.

## Why this driver prints two groups

The strengthened configuration is not submittable yet: `Palomar/LIXStrongSolution.lean`
proves each selected statement from one proposition the construction still
owes, so its theorems carry a hypothesis the challenge's do not and are named
`<theorem>_of`.  Comparing the two sides' theorem statements today would
therefore report a difference that is the honest state of the work.

What CAN be compared today, and is the defect that actually bit this
repository on 2026-09-10, is the **shared block**: `cornerDiag` and
`IsK1Injective`, written byte-identically in both files, elaborating to
different terms because the solution's environment reaches a Mathlib instance
the challenge's does not.  `cornerDiag` is in the compared closure of all three
theorems, so a difference there fails the real Comparator; `IsK1Injective` is
not, and is dumped anyway because it is the declaration that failed this way
before and is the cheapest canary for the next instance to do it.

So the report is in two groups, separated by `pending-boundary:`.  Everything
before the boundary is diffed against the Solution twin and gates;
everything after it is printed for inspection.  When the outstanding
proposition lands, the theorem names below lose their `_of` on the solution
side, the boundary moves to the end, and the whole report is diffed like the
other two pairs.

Run with `scripts/remote-build.sh --run scripts/PalomarLIXStrongChallengeType.lean`.
-/

open Lean Meta in
#eval show MetaM Unit from do
  -- `(true, n)` is a shared-block declaration, printed before the boundary and
  -- diffed against the twin; `(false, n)` is a compared statement, printed
  -- after it and reported without gating.  One flat list and one inline body,
  -- matching `scripts/PalomarLIXChallengeType.lean` exactly, so that the two
  -- drivers cannot drift in how they walk the closure.
  let targets : List (Bool × Name) :=
    [(true,  `ProblemLIXStrong.cornerDiag),
     (true,  `ProblemLIXStrong.IsK1Injective),
     (false, `ProblemLIXStrong.exists_simple_separable_powers_outside_U0),
     (false, `ProblemLIXStrong.exists_simple_separable_order_six_witness),
     (false, `ProblemLIXStrong.exists_simple_separable_squarefree_witness)]
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
