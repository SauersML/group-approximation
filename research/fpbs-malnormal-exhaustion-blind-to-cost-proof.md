---
rg: 2
id: fpbs-malnormal-exhaustion-blind-to-cost-proof
kind: route
title: Reidemeister-Schreier and Gaboriau VI.9 for W1, Hopficity and a malnormality case check for stage relations
target: fpbs-malnormal-exhaustion-blind-to-cost
requires: []
artifacts:
  - research/artifacts/fpbs-malnormal-exhaustion-calibration-2026-09-17.md
---

Direct proof, in artifact sections 1–3.

- **Item 1.** `ker(F_2 -> Z)` is free on `x_k = b^k a b^{-k}`
  (Reidemeister–Schreier). The stages `S_n = <x_{-n}, ..., x_n>` are free
  factors, hence malnormal, and for `L <= S` with `S` malnormal and `g` outside
  `S`, `L ∩ g L g^{-1} <= S ∩ g S g^{-1} = 1`, so wq-normal hulls and chains
  stay in a stage. [G00] Prop VI.9 gives cost infinity for every free action.
  Proposition 2 is the contrapositive: an argument from H and (P1)–(P7) to
  finite cost would apply to `W1`.
- **Item 2.** If `rank G = rank H + 1`, `H * <t> -> G` is a surjection between
  free groups of equal finite rank, hence injective (Hopfian). If
  `rank G <= rank H`, rank invariance forces a nontrivial kernel. A cyclically
  reduced kernel element with at most 2 `t`-letters has one of the forms
  `t^e h`, `t^{±1} h t^{∓1} h'`, `t^{±1} h t^{±1} h'`; each gives a nontrivial
  element of `H ∩ u H u^{-1}` with `u` outside `H` (in the last case
  `u = t^{±1} h` and `u^2` is nontrivial by torsion-freeness), contradicting
  malnormality. Sharpness: `t a t^{-2} b_{m-1}^{-1}` with `t = b_m`, using
  `b_{m-1} = b_m a b_m^{-2}` and malnormality of `<a, b a b^{-2}>` in `<a, b>`
  (Stallings graph; the off-diagonal part of the fiber product is a forest).
