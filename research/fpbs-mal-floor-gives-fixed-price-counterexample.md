---
rg: 2
id: fpbs-mal-floor-gives-fixed-price-counterexample
kind: route
title: The single-stage floor makes Gamma_mal a group with a free action of cost 2 and a free action of infinite cost
target: fpbs-fixed-price-counterexample-exists
requires:
  - fpbs-mal-bernoulli-single-stage-floor
  - fpbs-mal-fixed-price-iff-bernoulli-finite-cost
  - fpbs-mal-odometer-product-actions-have-cost-two
artifacts:
  - research/artifacts/fpbs-finite-cost-transfers-up-weak-containment-2026-09-18.md
  - research/artifacts/fpbs-shifted-stage-relative-cost-zero-or-infinite-2026-09-17.md
---

This route makes the open floor the only missing premise of the flagship's
negation. Before it, the equivalence "floor iff Gamma_mal fails fixed price"
was ESTABLISHED, but nothing wired it into
`fpbs-fixed-price-counterexample-exists`.

Let `Gamma_mal = <a, b_1, b_2, ... | b_k = b_{k+1} a b_{k+1}^{-2}>`, with
`H_1 = <a, b_1>` and `β` its Bernoulli shift.

- **Group.** `Gamma_mal` is countably infinite. It is the ascending union of
  the rank-2 free groups `H_n`.
- **Expensive action.** Assume `fpbs-mal-bernoulli-single-stage-floor`, that
  is, `relC(E_β; E_{β|H_1}) > 0`. Then item 6 of
  `fpbs-mal-fixed-price-iff-bernoulli-finite-cost` fails. So item 2 fails,
  and `C(β) = ∞`. The mechanism is the stage-shift dichotomy of the second
  artifact, which says relC over a stage is 0 or ∞. `β` is free.
- **Cheap action.** By `fpbs-mal-odometer-product-actions-have-cost-two`,
  each odometer product `β × Ẑ_χ` is a free p.m.p. action of cost 2.
- **Conclusion.** `Gamma_mal` has two free p.m.p. actions whose costs differ,
  `∞` and `2`. This is `fpbs-fixed-price-counterexample-exists`.

The third premise is not logically needed. The equivalence alone gives
"Gamma_mal fails fixed price". It is listed because it names an explicit
cheap witness, so the counterexample is concrete.

**Status.** The route is live exactly when the floor is. The floor's open
content is `inf_j Q_j > 0`. It splits into D0 (`Q_0 > 0`) and D1 (depth
uniformity); see `fpbs-mal-floor-iff-deep-promotion-floor`.
