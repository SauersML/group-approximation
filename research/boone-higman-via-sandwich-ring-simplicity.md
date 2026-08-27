---
rg: 2
id: boone-higman-via-sandwich-ring-simplicity
kind: route
title: Make the coefficient element full by one universal relation and read off a simple elementary group
target: boone-higman-conjecture
requires: []
artifacts:
  - research/artifacts/boone-higman-audit-2026-08-17.md
---

The shortcut this region has to close, because
`universal-sandwich-ring-is-finitely-presented-and-injective` makes it look
available.

Take `R = Z[G~]` and `r = 1 - g`, form the finitely presented ring
`U = R<p,q>/(prq-1)`, note that `r` is full in `U`, note by
`normal-generation-makes-the-augmentation-ideal-one-generated` that *every*
`1 - s` with `s` a nontrivial element of the simple core is then full too,
conclude that `U` is simple or close enough, and take `EL_4(U)` — a finitely
presented, property (T), simple group containing the original group.  No
maximal quotient, no Zorn, no kernel problem.

Dead at `one-sided-sandwich-leaves-an-ideal-missing-the-core`.  Fullness of
every `1 - s` controls only ideals meeting the coefficient ring, and the
Toeplitz example exhibits a nonzero proper ideal `J` with `J ∩ R = 0` in the
smallest instance of the construction.  The step from "every core element is
full" to "every nonzero element is full" is not an inference; it is the thing
that would have to be proved.

**What survives the demolition.**  The finite-presentation half, entirely.
`universal-sandwich-ring-is-finitely-presented-and-injective` remains true
and remains the strongest new statement in this region — it removes the
Shalom cover from the envelope construction and lets
`ck-envelope-has-a-finitely-normally-generated-maximal-kernel` be posed about
`EL_4(U)` for an explicit finitely presented `U`.  What dies is only the hope
that the same relation delivers simplicity for free.

**Why the ideal-lattice version is no easier than the group version.**  Even
granting a maximal two-sided ideal `I ⊂ U` with `I ∩ R = 0`, the quotient
`U/I` is simple, but finite presentability of `U/I` is equivalent to finite
generation of `I` as a two-sided ideal — the exact ring analogue of
`fp-quotient-iff-kernel-finitely-normally-generated`.  So
this route does not sidestep the obstruction; it restates it one category
over.  The live successor is
`boone-higman-via-finitely-presented-simple-ring-quotient`, which asks for
the missing finiteness directly.
