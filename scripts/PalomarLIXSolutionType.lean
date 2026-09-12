import Palomar.LIXSolution

/-!
# Dump the three compared LIX statements and their declaration closures

`leanprover/comparator` decides a submission by comparing the exported
Challenge and Solution `ConstantVal`s structurally -- not up to definitional
unfolding -- and then walking the constants each compared type mentions,
transitively, requiring each ordinary declaration to be IDENTICAL in both
environments.  Identical means name, type **and value**.

The driver hashes both types and values because identical source can elaborate
differently when the two modules import different instances.

So this walks the same closure Comparator walks and prints, for every constant
in it, the structural hash of its type and of its value.  Its Challenge twin
prints the same, and `scripts/check_palomar_statement_match.sh` diffs them.

`Palomar/comparator-lix.json` selects three theorems, so one `declaration:`
section is printed per theorem, in the order the configuration lists them.  The
order matters: the twin prints the same three sections in the same order and
the comparison is a plain diff, so a driver that iterated a set rather than a
list could report a difference that is only a permutation.

Run with `scripts/remote-build.sh --run scripts/PalomarLIXSolutionType.lean`.
-/

open Lean Meta in
#eval show MetaM Unit from do
  let targets : List Name :=
    [`ProblemLIX.not_all_simple_unital_k1Injective,
     `ProblemLIX.exists_separable_simple_not_k1Injective,
     `ProblemLIX.exists_separable_simple_stage_two_witness]
  let env ← getEnv
  for target in targets do
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
