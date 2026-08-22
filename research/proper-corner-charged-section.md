---
rg: 2
id: proper-corner-charged-section
kind: claim
title: Expose Schur phase through a one-sided charged section into a proper corner
distinct_from:
  central-square-orients-transverse-ledger: that supplies the orientation clause after a charged lift exists; this asks for the only carrier geometry not ruled out by gauge neutrality and Morita cancellation.
  atlas-rectangular-wedderburn-isometry-certificate: that permits finite-dimensional coordinate selection but forbids a universal algebraic rectangular isometry; this asks for a group-word compressed section whose finite and properly infinite models behave differently.
---

# Expose Schur phase through a one-sided charged section into a proper corner

Construct packet projections `p<q`, a group word `t`, and a raw charged return
`W` on `p` such that finite-matrix correction yields

```text
v=qtp,       v^*v approximately p,       vv^* approximately r<q,
```

with `q-r` of fixed positive normalized trace, while the exact properly
infinite marked model realizes the required one-sided equivalence and keeps
`J` nontrivial. The charged square clause on the source must orient the
transverse ledger without extending `v` to a unitary equivalence of the full
`q` carrier.

This is the only raw-lift geometry left by
`projective-gauge-charge-forces-morita-or-corner`. Equal full carriers give
Morita matrix units; neutral same-carrier expressions remain phase-blind.

## Attempts

- The binary Leavitt prefix connector now supplies the exact uncharged
  proper-corner ledger.  By
  `one-sided-leavitt-connector-has-sharp-overlap-payment`, the fixed
  three-root word built from `x=s_(00)t_0`, `y=s_0t_(00)` conjugates the
  coarse corner `Q=f_0+f_1` to `P=f_0`, and every finite tracial realization
  pays
  `tau(f_1)<=||UQU^*-P||_2^2`.  The properly infinite Leavitt model realizes
  the connector exactly.  What remains is not the connector or its Gram
  estimate: it is making the fine support reflection `1-2f_0` an ordinary
  same-carrier word without the arbitrary Clifford multiplicity twist.
- A reverse full Schur edge exposes the phase but generates the full branch
  `M_2`, by `two-chart-square-lift-recreates-schur-m2`.
- A projective Atlas rectangle is either flat on the canonical common-`U`
  lift or depends on an independent factor gauge.
- A universal exact rectangular isometry contradicts finite-factor trace
  monotonicity. The viable statement must emerge only after finite-matrix HS
  correction or from a genuinely nonunital/properly infinite corner packet.
- The direct binary Toeplitz section is now ruled out by
  `toeplitz-child-section-loses-square-or-exit`. A nonreducing closed loop has
  an uncontrolled cross term in its compressed square; if its compression is
  unitary, the source corner reduces the loop and the complementary child is
  an unpaid spectator. The missing ingredient is therefore a matrix-only
  positive Gram/support correction, not another ordinary square relation.
- Making the return involutive does turn the cross term into the positive
  Gram `L=p-(php)^2`, but
  `involutive-compression-gram-ledger-has-unit-loss` proves the resulting
  recurrence coefficient is sharply one. The regular stationary ray has
  equal positive branch mass and `L=0`. Any viable correction must add a
  mixed support test correlating that complement with `L`; positivity alone
  is insufficient.
- The current phase-even Atlas candidates do not supply that mixed test.
  `atlas-even-gram-does-not-pay-toeplitz-exit` shows that the common quarter
  carrier is transverse to the child algebra, the mixed `C_3` Gram has a
  collision-regular zero, and q14's positive wall has an exact finite-factor
  escape after tensoring with the Toeplitz spectator. What remains possible
  is only a matrix-specific adaptive Wedderburn/support selection.
