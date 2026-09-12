---
rg: 2
id: fpbs-amenable-wq-normal-class-via-relative-susceptibility
kind: route
title: Apply the relative-susceptibility equivalence to every Cayley graph of the class
target: fpbs-amenable-wq-normal-class-nonuniqueness
requires:
  - fpbs-bs-iff-finite-relative-susceptibility
  - fpbs-amenable-wq-normal-relative-subcriticality
---

Fix `Gamma` in the class, an infinite amenable wq-normal subgroup `H`, and a
finite generating set `S`. The premise
`fpbs-amenable-wq-normal-relative-subcriticality` supplies `p > p_c(Cay(Gamma,S))`
with `E_p|K_o ∩ H| < infinity`. The implication (2 ⇒ 1) of
`fpbs-bs-iff-finite-relative-susceptibility` then gives `p_c < p_u` for
`Cay(Gamma,S)`. Since `S` was arbitrary, the target follows.
