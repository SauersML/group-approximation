---
rg: 2
id: spectral-recurrence-power-return-non-mf-criterion
kind: claim
title: Uniformly authenticated conjugacy-to-power returns force operator-norm non-MF
artifacts:
  - GroupApproximation/Sofic/NoRenormalizationCapacity.lean
distinct_from:
  self-hashed-adversarial-collision-forces-mf-collapse: that is the general palette/collision capacity theorem; this specializes finite capacity to recurrence of one unitary's spectrum and needs no packet family.
  threshold-free-mf-compiler-equivalence: that extracts no analytic obstruction beyond a seed; this conditional criterion supplies a genuinely operator-norm obstruction if UPR is constructed.
  conjugacy-addressed-opnorm-challenges-are-lossless: that proves only zero-loss transport of a relator under conjugation; this also compares the transported word with an unbounded power of one cursor.
---

Let `Gamma=<S|R>` be finitely presented, and let `w!=1`.  Suppose there are
words `a_m` and one constant `C`, independent of `m`, such that every finite
unitary tuple satisfies

```text
||a_m(U) w(U) a_m(U)^-1 - w(U)^m||_op <= C Def_R(U).
```

Then every norm-corona homomorphism kills `w`, so `Gamma` is non-MF.

This is a conditional criterion, not an unconditional construction.  Its only
open construction input is `uniform-power-return-self-hash`; the recurrence
and contradiction after UPR are elementary and do not invoke property `(T)`,
Hilbert--Schmidt norm, projections, finite central subgroups, or
renormalization.  The frozen-coordinate quantitative contradiction is
kernel-checked as
`NoRenormalizationCapacity.no_model_of_recurrent_uniform_power_return`, and
its composition with finite-dimensional recurrence is kernel-checked as
`NoRenormalizationCapacity.no_model_of_uniform_power_return`.
