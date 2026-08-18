/-
Portions adapted from `PrimeGapsCert/Meta/Batched.lean` in PrimeGapsLib.
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.

The original PrimeGapsLib command generates consecutively indexed kernel
`decide` theorems and assembles them into a balanced dependent function.  This
adaptation keeps that design, renames it for general use in GroupApproximation,
and adds an `except` form so an unusually expensive case can be discharged by
a separately sharded kernel proof.
-/

import Lean.Elab.Command

open Lean Meta Elab Term Command

namespace GroupApproximation

/-- Generate consecutively indexed theorem cases, each checked by kernel `decide`. -/
elab "mk_kernel_batched_theorem" count:num fi:ident : command => do
  let count := count.getNat
  let f := fi.getId
  let [(_, [])] ← resolveGlobalName f | throwError "Invalid theorem family"
  for i in List.range count do
    let thmName := mkIdent (f.str s!"case_{i}")
    elabCommand <| ←
      `(command| theorem $thmName : $fi $(quote i) := by decide +kernel)

/-- As `mk_kernel_batched_theorem`, but leave one case for a custom proof. -/
elab "mk_kernel_batched_theorem_except" count:num skip:num fi:ident : command => do
  let count := count.getNat
  let skip := skip.getNat
  if skip >= count then
    throwError "Skipped case {skip} is outside batch of size {count}"
  let f := fi.getId
  let [(_, [])] ← resolveGlobalName f | throwError "Invalid theorem family"
  for i in List.range count do
    unless i = skip do
      let thmName := mkIdent (f.str s!"case_{i}")
      elabCommand <| ←
        `(command| theorem $thmName : $fi $(quote i) := by decide +kernel)

namespace BatchedKernelChecks

/-- Assemble a dependent function on `Fin 1` from its value at zero. -/
def finOne {motive : Fin 1 → Sort*} (zero : motive 0) : ∀ i, motive i :=
  fun i ↦ Fin.cases zero (fun j ↦ Fin.elim0 j) i

/-- Assemble a dependent function on `Fin (m + n)` from its two summands. -/
def finAdd {m n : Nat} {motive : Fin (m + n) → Sort*}
    (left : ∀ i, motive (Fin.castAdd n i))
    (right : ∀ i, motive (Fin.natAdd m i)) : ∀ i, motive i :=
  fun i ↦ Fin.addCases left right i

end BatchedKernelChecks

private meta def batchedProofTree
    (theoremNames : Array Name) (start size : Nat) : String :=
  if size = 0 then
    "fun i ↦ Fin.elim0 i"
  else if size = 1 then
    s!"GroupApproximation.BatchedKernelChecks.finOne {theoremNames[start]!}"
  else
    let leftSize := size / 2
    let rightSize := size - leftSize
    s!"GroupApproximation.BatchedKernelChecks.finAdd \
      ({batchedProofTree theoremNames start leftSize}) \
      ({batchedProofTree theoremNames (start + leftSize) rightSize})"

/-- Assemble all cases generated for one indexed theorem family into a function. -/
elab "combine_kernel_batched_theorems%" family:ident count:num : term <= expectedType => do
  let [(theoremName, [])] ← resolveGlobalName family.getId
    | throwError "Expected one unambiguous theorem family"
  let env ← getEnv
  let mut theoremNames : Array Name := #[]
  for i in [:count.getNat] do
    let caseName := theoremName.str s!"case_{i}"
    unless env.contains caseName do
      throwError "Unknown batched theorem `{caseName}`"
    theoremNames := theoremNames.push caseName
  let source := batchedProofTree theoremNames 0 count.getNat
  let .ok termSyntax := Parser.runParserCategory env `term source
    | throwError "Failed to construct the batched proof function"
  withOptions (fun options ↦ options.set `exponentiation.threshold 3000) do
    elabTerm termSyntax expectedType

end GroupApproximation
