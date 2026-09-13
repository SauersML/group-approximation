import Palomar.BlanchardToeplitzChallenge

/-!
# Dump the Blanchard Question 5.4 statement and its declaration closure

The challenge-side driver for `Palomar/comparator-blanchard-toeplitz.json`, twin of
`scripts/PalomarBlanchardToeplitzSolutionType.lean`.

`leanprover/comparator` compares the exported challenge and solution
`ConstantVal`s structurally and then walks the constants each compared type
mentions, transitively, requiring each to be identical in both environments:
name, type and value.  For the definitions of the shared block and the compared
theorem this driver prints the level parameters, the type hash, the transitive
closure with a type and value hash per constant, and the `pp.all` type, and
`scripts/check_palomar_statement_match.sh` diffs the two drivers' output.

The shared block defines no structures, so no constructors are listed.  The
values of the definitions are walked as well, because Comparator compares them;
the proof of the theorem is not, because the challenge states it with a hole.

Run with `lake env lean scripts/PalomarBlanchardToeplitzChallengeType.lean`.
-/

open Lean Meta in
#eval show MetaM Unit from do
  let targets : List (Bool × Name) :=
    [(true,  `BlanchardToeplitz.L2),
     (true,  `BlanchardToeplitz.HilbertCube),
     (true,  `BlanchardToeplitz.cubeDist),
     (true,  `BlanchardToeplitz.instTopologicalSpaceHilbertCube),
     (true,  `BlanchardToeplitz.K),
     (true,  `BlanchardToeplitz.Sections),
     (true,  `BlanchardToeplitz.etaCoord),
     (true,  `BlanchardToeplitz.continuousSections),
     (true,  `BlanchardToeplitz.etaMultiples),
     (true,  `BlanchardToeplitz.moduleF),
     (true,  `BlanchardToeplitz.ddModule),
     (true,  `BlanchardToeplitz.Fock),
     (true,  `BlanchardToeplitz.tensorCoord),
     (true,  `BlanchardToeplitz.fockGenerators),
     (true,  `BlanchardToeplitz.fockModule),
     (true,  `BlanchardToeplitz.IsSectionAdjoint),
     (true,  `BlanchardToeplitz.toeplitzAlgebra),
     (true,  `BlanchardToeplitz.IsProperlyInfiniteSet),
     (false, `BlanchardToeplitz.blanchard_question_5_4)]
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
