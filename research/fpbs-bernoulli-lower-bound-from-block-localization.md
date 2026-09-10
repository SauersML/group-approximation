---
rg: 2
id: fpbs-bernoulli-lower-bound-from-block-localization
kind: route
title: Round localized relative cycle surplus on the projection to a Bernoulli action
target: fpbs-free-action-cost-at-least-bernoulli-cost
requires:
  - fpbs-relative-cycle-block-localization
  - fpbs-relative-cycle-block-rounding-bound
artifacts:
  - research/artifacts/fpbs/docs/relative-cycle-exchange.md
---

Apply localization to pi:a x b->b, where a is an arbitrary free action
and b a Bernoulli action of the finitely generated group. The rounding
bound gives generating base graphings of cost at most c(Phi_n) plus
an error tending to zero. Hence C(b)<=C(a x b). Lifting graphings of
a to the diagonal product action gives C(a x b)<=C(a). This proves the
required reverse inequality, conditional on the explicitly open
localization premise. No cost--Betti equality is needed, and the
separate countable-group passage remains open.
