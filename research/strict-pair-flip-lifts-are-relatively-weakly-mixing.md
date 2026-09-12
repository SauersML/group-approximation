---
rg: 2
id: strict-pair-flip-lifts-are-relatively-weakly-mixing
kind: claim
title: The flip lift of a strict split pair is a relatively weakly mixing extension of the Bernoulli base
distinct_from:
  strict-split-pairs-carry-positive-entropy-flip-lifts: that constructs the flip lift and bounds its conditional one-site entropy from below; this proves the resulting extension of the Bernoulli base is relatively weakly mixing, a relative factor of an i.i.d. product extension.
  kazhdan-map-bernoulli-finite-extensions-are-trivial: that collapses finite-to-one extensions of the Bernoulli base over Kazhdan hosts; this shows the extensions strict pairs actually carry are of the relatively weakly mixing kind that superrigidity cannot collapse.
artifacts:
  - research/artifacts/kazhdan-superrigidity-bernoulli-extensions-2026-09-12.md
  - research/artifacts/decoder-fiber-flip-lifts-2026-09-12.md
---

ESTABLISHED. Let `G` be any countable group, and `tau, sigma` a strict split pair over `G`. Let
`nu = F_* P` be the flip lift of `strict-split-pairs-carry-positive-entropy-flip-lifts`, and
`lambda` the uniform Bernoulli measure. Then `sigma: (A^G, nu) -> (A^G, lambda)` is a relatively
weakly mixing extension. It is an intermediate factor of the product extension
`(A^G x [0,1]^G x {0,1}^G, lambda (x) Leb^G (x) Bern(1/2)^G) -> (A^G, lambda)`, whose fibre process
is i.i.d. and independent of the base.

Proof: artifact Proposition 5.1. The equation `sigma o F = pr_1` places the lift between the
product extension and its base. The relative product of the product extension is
`X x Y x Y` with `Y` Bernoulli, which is ergodic because a weakly mixing system times an ergodic
system is ergodic. Relative products of intermediate factors are factors of it.

**Consequence for the Kazhdan attack.** Every strict pair, over every group, carries
positive-entropy extensions of the Bernoulli base of this relatively weakly mixing kind, and they
carry no cocycle into a finite or compact group. So cocycle superrigidity can never contradict a
strict pair. A lower bound on Bernoulli Rokhlin entropy over a Kazhdan host would have to control
the relative entropy of such extensions (artifact Section 5.3).
