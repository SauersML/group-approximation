import Palomar.Solution

/-!
# Dump the compared statement, as elaborated in the Challenge environment

`leanprover/comparator` compares the exported Challenge and Solution
statements with structural equality on `ConstantVal` -- not up to definitional
unfolding -- and then walks every constant the type mentions, requiring each to
be identical in both environments.  Nothing in an ordinary `lake build` looks
at that: both files compile whatever they say.

This driver and its Challenge twin print the same three things about the
compared declaration: the structural hash of its type, its fully explicit
pretty-printed form, and the sorted list of constants the type mentions.  The
two outputs must be identical.  `scripts/palomar_statement_diff.sh` runs both
and diffs them.

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
  let consts := info.type.getUsedConstants.qsort (·.lt ·)
  IO.println s!"usedConstants: {consts.size}"
  for c in consts do
    IO.println s!"  const {c}"
  let fmt ← withOptions
    (fun o => (o.setBool `pp.all true).setBool `pp.explicit true) do
      ppExpr info.type
  IO.println "type:"
  IO.println (toString fmt)
