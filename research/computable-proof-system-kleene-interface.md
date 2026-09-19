---
rg: 2
id: computable-proof-system-kleene-interface
kind: claim
title: Formal syntax for computably enumerable proof systems and a Kleene fixed-point operator
distinct_from:
  threshold-free-mf-compiler-equivalence: that node records the semantic fixed-point argument externally; this asks for the reusable Lean syntax and recursion infrastructure itself.
artifacts:
  - GroupApproximation/Computability/MFRadicalGodel.lean
---

`MFRadicalGodel.ProofSystem` packages a partial-recursive semidecision
procedure on Mathlib partial-recursive codes.  A code `c` names the formula
`MFRadicalComputer.codeWord c != 1`; `ProofSystem.Sound` records soundness only
for that formula family.  `diagonalSearch_partrec₂` proves uniform partial
recursiveness of proof search in the candidate self-code, and
`exists_proofSearch_fixedPoint` applies Mathlib's Kleene second recursion
theorem.

## Attempts

The earlier `reverseKleene_fixedPoint_logic` remains the proposition-level
semantic lemma.  The new interface is strictly stronger: it contains actual
program codes, a partial-recursive proof search, and an effective fixed point,
with no opaque recursion-theorem assumption.
