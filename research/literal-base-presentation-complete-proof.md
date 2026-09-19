---
rg: 2
id: literal-base-presentation-complete-proof
kind: route
title: Split the presented base into translation and rotation, then descend
target: literal-base-presentation-complete
requires: []
artifacts:
  - GroupApproximation/Monsters/LiteralBaseCompleteness.lean
  - GroupApproximation/Monsters/P13DescentMaster.lean
  - notes/E_SOFICITY_SELF_CONTAINED_2026-08-16.md
---

## Direct proof

Compiled, zero-input.  `LiteralBaseCompleteness.baseAffineEquiv` is
`MulEquiv.ofBijective affineQuotient` fed with `affineQuotient_injective` and
`affineQuotient_surjective`; surjectivity is the generator computation, and
injectivity is the assembly of four layers already in the tree:

1. `LiteralBaseTranslationNormal` and `LiteralBaseRotationRetract` give the
   semidirect skeleton of the PRESENTED base, reducing injectivity to the two
   factors separately.
2. `LiteralBaseP13RotationQuotient` maps the thirteen-relator Steinberg
   presentation onto the eight-relator rotation group by audited short words,
   surjectively.
3. `P13DescentMaster.toSL3_injective` — the in-repository completeness theorem
   for that Steinberg presentation — then forces the rotation matrix model
   `toSL3` to be injective, so the rotation factor of the presented base
   injects.
4. On the translation factor, the three commuting generators normal-form into
   `v_1^a v_2^b v_3^c`, and reading entries `(i,3)` of the affine matrix
   recovers `a`, `b`, `c`; the corner block recovers the rotation part.

An element with identity affine matrix therefore has trivial rotation part by
(3) and `a = b = c = 0` by (4), hence is trivial.

The mathematical statement is written out as Section 1 of
`notes/E_SOFICITY_SELF_CONTAINED_2026-08-16.md`.

## What it costs

Nothing external.  In particular this route does NOT use the classical
completeness of the eight-relator presentation of `SL_3(Z)` (\cite{CRW}
Theorem 2), which the manuscript quarantines at `rem:classical-base` as unused
literature; the P13 descent is proved in-repo.
