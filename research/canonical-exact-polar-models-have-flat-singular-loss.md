---
rg: 2
id: canonical-exact-polar-models-have-flat-singular-loss
kind: claim
title: Canonical exact polar models can have flat macroscopic singular loss
distinct_from:
  macroscopic-zero-compressions-make-polar-data-universal: that uses zero compressions whose polar extensions are arbitrary; this keeps every singular value at one prescribed `t in (0,1)`, making the polar correction unique and exact.
  fixed-projective-leak-forces-polar-singular-collapse: that proves a projective enemy must contain a bad singular block; this shows such a block, even with canonical character and zero relator defect, is not by itself evidence of a projective leak.
  leakage-small-polar-compressions-obey-projective-transfer: that closes the regime where singular loss tends to zero; this proves every fixed nonzero loss level admits exact canonical calibrations.
---

**ESTABLISHED.**  Let `A=SL_3(Z[1/2])`, let `S_A` be any fixed finite
symmetric packet of nonidentity elements, and fix `0<t<1`.  There are exact
finite-dimensional representations `rho_n` with character converging to the
regular character, exact ambient representations `pi_n`, and
positive-density projections `P_n` such that, after identifying `P_nH_n`
with the space of `rho_n`,

```text
P_n pi_n(s) P_n = t rho_n(s)                 (s in S_A). (FSL1)
```

Consequently the unique unitary polar correction of every compressed
generator is exactly `rho_n(s)`.  All arithmetic relators have zero defect,
while every singular value of every named compression equals `t` and

```text
||(1-P_n)pi_n(s)P_n||_HS^2/rank(P_n)=1-t^2.             (FSL2)
```

Thus positive-mass singular collapse cannot be charged to finite arithmetic
relator defect, even under canonical character, positive retained density,
nonzero singular overlap, and a unique polar factor.  The singular block
extracted from a projective-transfer enemy is only a necessary location of
information loss.  A valid next inequality must also use the projective
witness `U` and its joint incidence with the raw compression; singular data
and arithmetic relators alone are insufficient.

These models are not projective-transfer counterexamples.  Since `rho_n` is
exact, the established exact transfer theorem prevents a unitary from being
projectively central on `rho_n(C)` while leaking at `rho_n(h)`.

