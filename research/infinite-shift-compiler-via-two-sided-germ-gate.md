---
rg: 2
id: infinite-shift-compiler-via-two-sided-germ-gate
kind: route
title: Choose an enumeration passing the two-sided germ gate, then lift finite presentation from the germ group to the envelope
target: infinite-shift-higman-compiler
requires:
  - decidable-inputs-admit-two-sided-fg-near-index-kernel
  - mz-germ-finite-presentation-lifts-to-the-envelope
artifacts:
  - research/artifacts/boone-higman-mz-antitwisted-germ-gate-2026-09-17.md
---

Let `P` be an infinite finitely presented group with decidable word problem.

1. `decidable-inputs-admit-two-sided-fg-near-index-kernel` supplies `nu` with `R_nu` finitely presented and
   `ker eta` finitely generated.
2. `mz-germ-finite-presentation-lifts-to-the-envelope`, applied to this `(P, nu)`, gives that `E_nu(P)` is finitely
   presented. That is the target. QED

**Why this decomposition is sharp.** By the established
`mz-envelope-fp-forces-two-sided-fg-near-index-kernel`, the first prerequisite is necessary for the target. It is
equivalent to finite presentation of `E_nu(P)/FSym(N)`, so no route to the compiler avoids it.

The second prerequisite is the whole remaining gap between germs and permutations, stated uniformly in `(P, nu)`.
The two prerequisites fail independently:
- the first is a condition on the input `P` over all its enumerations;
- the second is a single-pair statement that one counterexample refutes.

The first prerequisite has two separately failing clauses:
- (G1) `[eta], [-eta] ∈ Σ^1(R_nu)`;
- (G2) `R_nu` finitely presented.

The square spiral enumeration of `Z^2` passes the one-sided shell window (`square-spiral-z2-enumeration-passes-the-finite-window-gate`) but dies at (G2).
