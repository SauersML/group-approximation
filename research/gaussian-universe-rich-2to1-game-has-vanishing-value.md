---
rg: 2
id: gaussian-universe-rich-2to1-game-has-vanishing-value
kind: claim
title: The Gaussian pair-sum universe rich 2-to-1 game, with left vertex a d x 2n standard Gaussian matrix G and right vertex its pair sums G M_P, has integral value at most (4 (1/(2n) + e^2 D (ln 2n)^D/(2n) + lambda_D(n)))^(1/4) for every D and every d, so its value tends to 0 uniformly in d
distinct_from:
  rotated-frame-universe-rich-2to1-game-has-vanishing-value: that is the Haar-frame game U_n with orthonormal left frames; this is the Gaussian game, whose left columns are only asymptotically orthonormal. Its pair-resampling walk is a second quantisation, which the frame walk is not. The frame statement stays open.
  pair-resampling-walk-balanced-partitions-are-unstable: that is the stability statement for the Haar-frame walk; this proves the analogous stability bound for the Gaussian walk, by chaos decomposition, and does not decide the frame case.
  rotated-frame-value-reduces-to-partition-stability: that proves val^4 <= 4 Stab for the frame game; this reuses its argument verbatim in the Gaussian model and then proves the stability bound.
  walsh-frame-rich-2to1-games-have-value-near-one: that shows Walsh frames give value near 1; this gives a rich universe of value near 0.
artifacts:
  - experiments/gaussian-rich-2to1-universe-2026-09-17/check_gaussian_universe.py
---

**ESTABLISHED.** Proof: route `gaussian-universe-vanishing-value-via-chaos-hypercontractivity`.

**The game `Gamma_(n,d)`.** Fix `n >= 2` and `d >= 1`.

* **Left vertices.** Matrices `G in R^(d x 2n)` with iid `N(0,1)` entries.
  Column `a` is `g_a`.
* **Edges.** A uniform labelled 2-to-1 map `P : [2n] -> [n]`, independent of
  `G`. `M_P in {0,1}^(2n x n)` is its incidence matrix.
* **Right vertex.** `H = G M_P`, so `h_b = g_a + g_a'` where `P^-1(b) = {a, a'}`.
* **Constraint.** Label `a` and label `b` are consistent iff `P(a) = b`.

`val(Gamma_(n,d))` is the supremum of `Pr[P(A(G)) = B(H)]` over Borel
`A : R^(d x 2n) -> [2n]` and `B : R^(d x n) -> [n]`.

**Richness.** For each fixed `P`, the columns of `H` are iid `N(0, 2 I_d)`.
So the law of `H` does not depend on `P`, and `P` is uniform and independent
of `H`. It is also independent of `G` by construction. So the pairing at a
random edge of any vertex is uniform.

**Theorem.** For every `n >= 2`, `d >= 1` and `D >= 1`,

`val(Gamma_(n,d))^4 <= 4 ( 1/(2n) + e^2 D (ln 2n)^D / (2n) + lambda_D(n) )`,

where `lambda_D(n)` is the operator norm of
`gaussian-pair-sum-chaos-eigenvalues-halve-every-two-degrees`.
By that claim, `limsup_n sup_d val(Gamma_(n,d)) <= 2^(-ceil(D/2)/4) 4^(1/4)`
for every `D`. Hence `sup_(d >= 1) val(Gamma_(n,d)) -> 0` as `n -> infinity`.

**Rate.** Taking `D ~ c ln n / ln ln n` gives a bound of order
`exp(-c' ln n / ln ln n)`. That is slower than any power of `n`. The linear
strategy of the artifact has value about `n^(-0.24)`, and nothing faster is
claimed.

**Where the frame model differs.** For Haar frames (`d = 2n`), `T_P` averages
a random rotation of the pair differences. Its restriction to each chaos-like
degree is not `I tensor M_D`: rotation averages carry Brauer-type invariants
built from the frame constraint `X X^T = I`. The Gaussian model removes that
constraint and keeps everything the reduction uses. So it answers the evidence
question with a different universe, and leaves the frame question open.
