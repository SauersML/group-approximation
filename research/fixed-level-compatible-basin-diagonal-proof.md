---
rg: 2
id: fixed-level-compatible-basin-diagonal-proof
kind: route
title: Track bounded-cycle shadowing through the fixed-level stability radius
target: fixed-level-bs14-compatible-basin
requires:
  - bs14-long-cycles-admit-bounded-period-shadowing
  - iwahori-square-root-presentation-is-bs14-plus-one-involution
  - bounded-period-iwahori-quotients-are-finite
  - one-unipotent-quotients-are-bounded-congruence
  - bounded-cycle-level-has-only-polylogarithmic-error
  - regular-bs14-cores-admit-dyadic-one-power-shadows
  - bs14-one-power-level-is-a-native-short-commutator
  - native-bs-level-has-strict-square-root-counterpackets
  - induced-rounding-needs-rms-section-fillings
  - repeated-squaring-and-tau-do-not-supply-the-moving-basin
---

An orbit of length `m<=K` has `S`-eigenvalues of order dividing `4^m-1`,
which proves `S_K^N_K=1`.  There is no need to quantize scalar return
monodromy: by `bounded-period-iwahori-quotients-are-finite`, the one-power
quotient `Gamma/<<s^N_K>>` is already finite.  This gives
`(FLB2)--(FLB3)`.

Finite-group normalized-HS stability supplies the fixed-level radius and
flexible modulus used below; they are no longer hypotheses.  Their
dependence on `K` is uncontrolled.

Changing `R,S` by bounded-cycle shadowing while leaving `x` fixed changes
each of the four bounded-length relative words by at most a universal
word-Lipschitz constant times the square roots of `(BCT2)`, giving `(FLB4)`.
Under `(FLB5)`, choose `j` and then take the original defect below
`alpha_j`; the fixed-level theorem applies at defect at most `2alpha_j`.
Sending `j` to infinity gives the asserted flexible repair.

Conversely, pointwise positivity of `delta_j` imposes no comparison with
`alpha_j`.  The scalar schedules `(FLB6)` prove the logical nonimplication:
for every fixed `j` there is a stability neighborhood, while no
preconditioned tuple is guaranteed to enter it.  This is a quantifier fence,
not a counterexample to the actual fixed-level groups.
