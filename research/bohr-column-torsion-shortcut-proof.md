---
rg: 2
id: bohr-column-torsion-shortcut-proof
kind: route
title: Follow the bounded-exponent route to the step where it stops
target: bohr-column-needs-more-than-bounded-exponent
requires: []
artifacts:
  - GroupApproximation/Sofic/AlternatingLampBohrResidual.lean
---

**Complete direct argument.**  Both halves are elementary.

*The exponent bound holds.*  `A_n^(X)` is a restricted direct sum, so an element
has finite support and its order is the lcm of finitely many element orders of
`A_n`, dividing `e = exp(A_n)`.  Continuity of `x |-> x^e` and closedness of
`{1}` in a Hausdorff group make `{x : x^e = 1}` closed, so it contains the
closure of any subset of itself.

*The conclusion does not follow.*  Even with `N = closure (f '' A_n^(X))`
profinite, triviality of `f '' A_n^(X)` is not implied: profinite groups have
plenty of nontrivial subgroups.  The finite-residual lever needs a finite
quotient of the ambient closure `closure (f '' W_n)`, whose exponent is
unbounded because it receives the acting group `V`.  So the bounded-exponent
hypothesis is discharged on the wrong group.

The module `Sofic/AlternatingLampBohrResidual` therefore states only what is
unconditional -- `Rad_Bohr(W_n) <= A_n^(X)`, and equality on profinite targets --
and states no form, conditional or otherwise, of the missing inclusion.
