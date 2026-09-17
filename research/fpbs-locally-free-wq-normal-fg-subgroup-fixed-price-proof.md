---
rg: 2
id: fpbs-locally-free-wq-normal-fg-subgroup-fixed-price-proof
kind: route
title: Bound every free action of the hull by the rank of the subgroup, then apply the c*-or-infinity dichotomy inside the hull
target: fpbs-locally-free-wq-normal-fg-subgroup-fixed-price
requires:
  - fpbs-wq-normal-subgroup-cost-transfer
  - fpbs-wq-normal-hull-is-almost-malnormal
  - fpbs-locally-free-free-action-costs-are-c-star-or-infinite
  - locally-free-groups-first-l2-betti-equals-c-star-minus-one
artifacts:
  - research/artifacts/fpbs-locally-free-fixed-pseudocost-2026-09-17.md
---

Complete proof.

**Item 1.** Let `1 != H <= Gamma` be finitely generated, of rank `d`. `Gamma` is
torsion-free, so `H` is infinite and almost malnormal subgroups are malnormal.
Put `W = W(H)`.
- The hull chain of `H` computed inside the group `W` is the chain computed in
  `Gamma`: at each stage every `g in Gamma` with `g W_beta g^(-1) ∩ W_beta`
  infinite already lies in `W_(beta+1) <= W`. So `H` has hull `W` in `W`.
- Let `b` be any free p.m.p. action of `W`. By `fpbs-wq-normal-subgroup-cost-transfer`
  applied to the group `W`, `C(b) <= C(b|H) <= d`.
- `W` is countably infinite and locally free (a subgroup of a locally free
  group). By `fpbs-locally-free-free-action-costs-are-c-star-or-infinite`,
  `C(b) in {c*(W), ∞}`. Since `C(b) <= d < ∞`, `C(b) = c*(W)`.
- So `W` has fixed price `c*(W) <= d`, and
  `c*(W) = 1 + beta_1^(2)(W)` by `locally-free-groups-first-l2-betti-equals-c-star-minus-one`.

**Item 2.** If `W(H) = Gamma`, item 1 with `W = Gamma` gives fixed price
`c*(Gamma) <= rk H`; in particular every free action has finite cost.

**Item 3.** Suppose no finitely generated subgroup has hull `Gamma`. Take the
compressed exhaustion `Delta_0 <= Delta_1 <= ...` of Lemma 2.1 of the artifact,
with `rk Delta_n <= c*`. Hulls are monotone (`H <= H'` implies
`W(H) <= W(H')`, since `W(H')` is an almost malnormal subgroup containing `H`,
by item 3 of `fpbs-wq-normal-hull-is-almost-malnormal`). So `M_n = W(Delta_n)`
increase, contain `Delta_n`, and exhaust `Gamma`. Each is proper by assumption,
malnormal by item 2 of the hull claim, and of fixed price `<= rk Delta_n <= c*`
by item 1. If the chain stabilized at `M_N`, then `Gamma = M_N` would be proper.

**Criterion.** If each generator `g` of `Delta_(n+1)` satisfies
`Delta_n ∩ g Delta_n g^(-1) != 1`, then by induction `Delta_n <= W(Delta_0)`
gives `W(Delta_0) ∩ g W(Delta_0) g^(-1) != 1`, hence `g in W(Delta_0)` by
malnormality; so `Delta_(n+1) <= W(Delta_0)`. For `a -> a^2, b -> b^2`, the
stage generators `a_(n+1), b_(n+1)` commute with `a_n = a_(n+1)^2`,
`b_n = b_(n+1)^2`. ∎
