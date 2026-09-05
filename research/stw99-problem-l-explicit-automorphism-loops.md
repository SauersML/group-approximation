---
rg: 2
id: stw99-problem-l-explicit-automorphism-loops
kind: claim
title: Construct explicit automorphism-loop generators for the rotation algebra or its Kirchberg counterpart (STW Problem L)
root: true
artifacts:
  - research/artifacts/stw99-actions-classification-cluster-2026-08-30.md
  - research/artifacts/stw50-rotation-loop-retraction-2026-09-04.md
  - research/artifacts/stw50-six-kirchberg-loops-2026-09-05.md
---

**Problem L of Schafhauser--Tikuisis--White, arXiv:2506.10902.**  Find
explicit loops generating `π_1(Aut(A_θ)) ≅ Z^6` (Gabe--Schafhauser in
progress, via the finite analogue of Dadarlat's
`π_k(Aut) ≅ KK^1(C_u A, S^k A)`), or of the matching UCT Kirchberg
algebra; more generally explicit `π_1(Aut(A))` generators for
UCT-Kirchberg or monotracial classifiable `A`.  STW: the rotation
action `T^2 ↷ A_θ` gives an injective `Z^2` (winding numbers through
`tr ∘ Bott ∘ ev`), proved below to be a direct summand.

The root's concrete target is the six-generator request with its
published **or** alternative. The invitation to treat other algebras
is a broader research direction, not a claim resolved for all algebras.

## Kirchberg alternative: six-loop construction (2026-09-05)

`stw50-six-kirchberg-circle-loops` gives six actual circle actions
whose invariant matrix is unimodular. The construction uses the
three-vertex graph with adjacency `[[2,1,2],[1,2,2],[1,1,3]]` and
the tensor square of the two-vertex graph with adjacency
`[[2,2],[1,3]]`, joined by one fixed unital classification
isomorphism. Edge phases and tensor-factor actions supply all six
integral directions in Dadarlat's natural loop invariant.

`stw50-kirchberg-kernel-loops-proof` constructs four explicit
products of these loops spanning the rotation-retraction kernel
after a fixed scaled K-theory identification with A_theta tensor
O_infinity. Appending them to the two canonical rotation loops
answers the Kirchberg alternative of the published request.

The classification isomorphisms are fixed nonconstructive choices;
no generator formulas for them are asserted. STW explicitly
contemplates classification identifications between models in
Section 14. The exact meaning of explicitness and all choices are
documented in the proof artifact. This is a written mathematical
proof, not a claim of independent expert or Lean verification.

The stably finite alternative remains a separate open root,
`stw50-stably-finite-six-loop-basis`. No explicit preimages of the
four additional loops in Aut(A_theta) are constructed here.

## Proved subsidiary question (2026-09-04)

`stw50-rotation-loops-form-a-direct-summand` proves the direct-summand
assertion explicitly raised by STW immediately before Problem L.
For an automorphism loop alpha, evaluate at U and V, translate both
unitary loops to basepoint 1, apply stabilized Bott, and extract the
coefficient of [1] in K_0(A_theta). The resulting homomorphism to Z^2
is a left inverse to the canonical rotation loops. The argument also
works on A_theta tensor O_infinity.

That earlier argument settled the subsidiary splitting question
without producing all six loops. If the Z^6 computation reported
by STW is used, the retraction identifies a complement isomorphic
to Z^4. The subsequent graph-model construction above supplies
its explicit basis in the Kirchberg counterpart.

## Attempts

For the stably finite alternative, the remaining task is still to
construct four explicit loops generating the retraction kernel.
Subtracting rotation coordinates normalizes a loop, but generation
needs its own integral argument.

The previous inner-loop bookkeeping was speculative: a map from inner
loops into pi_1(Aut(A_theta)) need not be injective, so its domain rank
cannot be counted as a new independent generator. Similarly, conjugating
by an SL_2(Z) symmetry does not by itself construct a based loop or
compute its integral homotopy class.

The new Kirchberg construction implements the graph-model strategy
with actual automorphism loops and the determinant-one computation;
it does not infer generation merely from the rank of a KK group.
