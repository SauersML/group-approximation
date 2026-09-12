---
rg: 2
id: median-matching-has-no-bernoulli-entropy-analogue
kind: claim
title: The median component-matching device degenerates on uniform Bernoulli shifts and on finite point sets
invalidates: [leavitt-zero-supremum-via-median-matching]
distinct_from:
  openai-bounded-median-component-matching: that is the device on almost-actions of finite sets, where it matches Kazhdan components; this shows its component observable is constant on the Bernoulli shift and its no-drift identity fails by a proportional boundary on finite point sets.
  sofic-radical-localizes-bernoulli-deficit-witnesses: that says collapse of some difference in every finite model is necessary for a deficit; this says the one mechanism producing that collapse over the Leavitt units supplies nothing beyond it.
  median-matching-transfers-to-bernoulli-partitions: that is the missing transfer a median-matching certificate would need; this is the established theorem refuting it.
artifacts:
  - research/artifacts/median-matching-entropy-translation-2026-09-12.md
---

Let `Gamma <= G` be nonamenable with finite symmetric generating set `S`, and let `X = (A^k)^G` be the
uniform Bernoulli shift.

1. **The shift.** For every `f in L^2(X)`,
   `||f - integral f||_2^2 <= kappa_S(Gamma)^-2 sum_(s in S) ||s.f - f||_2^2`, where `kappa_S(Gamma) > 0`
   is the spectral gap of `lambda_Gamma`. So every `Gamma`-invariant observable is constant.
2. **Finite pieces.** For every finite nonempty `P` in `G`, `|S P \ P| >= h_S(Gamma) |P|`, where
   `h_S(Gamma) > 0` is the Følner constant. On `P` the no-drift identity of the median device holds only
   up to a boundary term of size `|s P \ P|`.

So the device of `openai-bounded-median-component-matching` runs without content in both settings of a
Bernoulli deficit certificate.
* On the shift, the component observable and the median normalization are constant, and there is one
  component, so no matching.
* On a finite piece, the boundary error has the order of `|P|`, so coarea gives no concentration.

What the device contributes to a certificate over `L_(F_2)(1,2)^x` is invisibility of the defect in
finite models, which `sofic-radical-localizes-bernoulli-deficit-witnesses` already requires. It
constructs no partition. The missing transfer `median-matching-transfers-to-bernoulli-partitions` is
refuted by (1) and (2), and the route `leavitt-zero-supremum-via-median-matching` is dead.

Section 3 of the artifact records where the translation dies and what a construction would still need.

**ESTABLISHED 2026-09-12** by [[median-matching-has-no-bernoulli-entropy-analogue-proof]].
