---
rg: 2
id: padded-heat-equates-linear-logarithmic-schreier-seeds
kind: claim
title: Flexible SL5 stability and the linear and logarithmic universal-host seeds are equivalent
artifacts:
  - research/artifacts/sep7-padded-heat-linear-seed-self-improvement-2026-09-07.md
distinct_from:
  nonhyperlinear-sep7-logarithmic-seed: that asserts the still-open numerical spectral estimate for every small-defect tuple; this proves its equivalence to two other open assertions without asserting any of them.
  nonhyperlinear-sep7-osgood-extraction: that proves a conditional extraction theorem for any finite presentation; this uses rectangular heat to prove a converse for the specific SL5 universal-host seed.
  sln-z-flexibly-hs-stable: that asks for a stable SL_n(Z) at some rank at least three; this theorem concerns SL5 specifically and does not infer rank-five stability from an existential rank witness.
---

Fix the presentation, symmetric set S, and universal quotient Q_(2n) of
`moving-subgroup-schreier-correction-has-no-index-loss`. The following
three statements are equivalent:

1. SL_5(Z) is flexibly normalized-HS stable.
2. There are L,delta_*>0 such that every inverse-compatible U in U(n),
   in every dimension n, with 0<delta(U)<delta_* satisfies

```text
min Spec Delta_(Q_(2n),U) <= L^2 delta(U)^2.            (PHS1)
```

3. There are B,delta_*>0 such that every such U satisfies

```text
min Spec Delta_(Q_(2n),U)
 <= B delta(U)^2 log(e/delta(U)^2).                   (PHS2)
```

Here delta is the maximum normalized-HS defining-relator defect, and
Delta is the averaged rectangular coefficient connection Laplacian.
This is an equivalence theorem: all three assertions remain open.

The necessary direction is quantitative. Uniform presentation constants
eta_0,delta_0,L_0>0 exist such that a supplied exact representation rho
of dimension n<=D<=2n with full padded generator error at most eta_0
implies (PHS1), with L=L_0, whenever 0<delta(U)<delta_0. Neither
irreducibility nor a vanishing padding fraction is required for this
first-vector statement. It does not assert full linear correction.

Every flexibly correctable sequence eventually has these coarse padded
comparisons. Hence arbitrarily slow convergence of known corrections
cannot refute (PHS1) or (PHS2). A counterexample sequence with
min Spec Delta/delta^2 tending to infinity would instead stay outside
one fixed coarse correction basin and witness flexible instability.

DERIVATION
padded-rectangular-heat-seed-equivalence-proof
