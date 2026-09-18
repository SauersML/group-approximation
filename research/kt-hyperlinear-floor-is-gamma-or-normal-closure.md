---
rg: 2
id: kt-hyperlinear-floor-is-gamma-or-normal-closure
kind: claim
title: The Kun--Thom hyperlinear floor is Gamma or E, and per model the Laurent part of the commutant saturation is Gamma or E
distinct_from:
  kt-hyperlinear-floor-is-root-invisible-laurent-overgroup: that proves a trichotomy whose third alternative is a root-invisible overgroup strictly between Gamma and E; this shows that the third alternative is empty
  kt-pair-hyperlinear-floor-below-normal-closure: that asks whether some intermediate wreath W_Delta with E not in Delta is hyperlinear; this proves that the question is equivalent to W_Gamma being hyperlinear, without the compressor sandwich
  kt-ccr-iff-scalar-re-hull-contains-laurent-group: that relates (CCR) to the scalar-RE hull containing the Laurent group; this shows the hull is exactly Gamma or E, so one non-polynomial element of any shape decides it
  kt-compressor-commutant-collapse-is-all-or-nothing: that says the wall alternative has polynomial root content; this upgrades it to the statement that Gamma^sat meets E exactly in Gamma
---

**Setting.** As in `kt-hyperlinear-floor-is-root-invisible-laurent-overgroup`:
`Gamma = EL_r(R_+)`, `E = EL_r(R)`, `G = E ⋊ SL_d(Z)`, with `R_+ = F_q[x_1..x_d]` and
`R` its Laurent ring, `r,d >= 3`. `K_Gamma` is the least scalar-RE subgroup containing
`Gamma`, so `W_K` is hyperlinear iff `K_Gamma <= K`, for `K >= Gamma`.

**Theorem.**

1. **(Floor dichotomy.)** `K_Gamma = Gamma` or `K_Gamma = E`.
2. **(Weak target = strong target.)** If one element of `E \ Gamma` lies in `K_Gamma`,
   then `K_Gamma = E`. The shape of the element does not matter: it need not be a root,
   a torus or a unipotent.
3. **(Wreath equivalences.)** The following are equivalent: `W_Gamma` is hyperlinear;
   `K_Gamma = Gamma`; some `W_Delta` with `Gamma <= Delta <= G` and `E ⊄ Delta` is
   hyperlinear; every such `W_Delta` is hyperlinear. Hence
   `kt-pair-hyperlinear-floor-below-normal-closure` is equivalent to
   `hyperlinear-wreath-model` for this pair. Moreover, `W_Gamma` is non-hyperlinear iff
   `K_Gamma = E`, iff every canonical CE actor model satisfies the eight equivalent
   conditions of `kt-compressor-commutant-collapse-is-all-or-nothing`.
4. **(Per-model saturation dichotomy.)** For every group `U` and every homomorphism
   `π : G -> U`, let `Gamma^sat` be the set of `g` with `π(g)` commuting with
   `C_U(π(Gamma))`. Then `Gamma^sat ∩ E` is `Gamma` or `E`.

**Killed class.** No strategy for refuting (AC) or `hyperlinear-wreath-model` can work
through an intermediate overgroup strictly between `Gamma` and `E`. In the wall
alternative, a relative commutant that fails to be `E`-central is never centralised by
any non-polynomial matrix at all, not just by non-polynomial roots.

DERIVATION
kt-hyperlinear-floor-gamma-or-e-proof
