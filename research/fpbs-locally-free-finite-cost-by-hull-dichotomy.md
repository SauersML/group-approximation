---
rg: 2
id: fpbs-locally-free-finite-cost-by-hull-dichotomy
kind: route
title: Split locally free groups by whether some finitely generated subgroup has malnormal hull equal to the group
target: fpbs-locally-free-free-actions-have-finite-cost
requires:
  - fpbs-locally-free-wq-normal-fg-subgroup-fixed-price
  - fpbs-locally-free-malnormally-exhausted-finite-cost
---

Let `Gamma` be countably infinite and locally free with `c* < ∞`.

- **Some finitely generated `H` has `W(H) = Gamma`.** Item 2 of
  `fpbs-locally-free-wq-normal-fg-subgroup-fixed-price` gives cost `c*` for
  every free action.
- **No finitely generated subgroup has hull `Gamma`.** This is exactly the
  hypothesis of `fpbs-locally-free-malnormally-exhausted-finite-cost`.

The two cases are complementary, so the target follows from the two
prerequisites. The first is established; the second is open and contains
`Gamma_mal`.
