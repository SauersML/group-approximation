import Palomar.Solution

/-!
# Dump the compared statement and its declaration closure

`leanprover/comparator` decides a submission by comparing the exported
Challenge and Solution `ConstantVal`s structurally -- not up to definitional
unfolding -- and then walking the constants the compared type mentions,
transitively, requiring each ordinary declaration to be IDENTICAL in both
environments.  Identical means name, type **and value**.

An earlier version of this driver printed only the compared type and the names
of the constants it uses.  That was not enough, and the real Comparator said
so: with byte-identical source in both files, `ExplicitNonMF.relators`
elaborated to different values, because the Challenge saw only the instances
its own imports provide while the Solution saw Mathlib's
`FreeGroup.instDecidableEq` through the development.  Same text, same type,
different constant -- and a submission that would have been rejected after the
commit was public.

So this walks the same closure Comparator walks and prints, for every constant
in it, the structural hash of its type and of its value.  Its Challenge twin
prints the same, and `scripts/check_palomar_statement_match.sh` diffs them.

Run with `scripts/remote-build.sh --run scripts/PalomarSolutionType.lean`.
-/

open Lean Meta in
#eval show MetaM Unit from do
  let target : Name := `ExplicitNonMF.explicit_fp_sofic_hyperlinear_not_MF
  let env ← getEnv
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
