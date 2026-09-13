---
rg: 2
id: leavitt-hyperlinearity-eighteen-relator-unitary-test-proof
kind: route
title: Metric ultraproducts of unitary groups and simplicity of the presented group
target: leavitt-hyperlinearity-eighteen-relator-unitary-test
requires: [thompson-steinberg-presentation-of-leavitt-unit-group, binary-leavitt-unit-group-is-simple, hyperlinear-iff-group-factor-embeds-in-hyperfinite-ultrapower]
---

Let `Q` be the presented group. It is isomorphic to `L_(F_2)(1,2)^x`, which is countable and
simple. By `hyperlinear-iff-group-factor-embeds-in-hyperfinite-ultrapower` (item 1), a countable
group is hyperlinear iff it embeds in a metric ultraproduct
`U_omega = prod_omega U(d_k) / N_omega` with the normalized Hilbert--Schmidt metric.

(2 => 1). The classes `[A_k], [B_k], [C_k], [X_k]` kill every relator in `U_omega`, so they
define a homomorphism `Q -> U_omega`. The image of `x` is nontrivial, because `||X_k - I||_2`
stays bounded below. A nontrivial homomorphism from a simple group is injective, so `Q` embeds
and is hyperlinear.

(1 => 2). Embed `Q` in some `U_omega` and lift `a, b, c, x` to sequences of unitaries. Every
relator tends to `I` along `omega`, and `x != 1` gives `||X_k - I||_2 >= c_0 > 0` along `omega`.
Choose indices `k_1 < k_2 < ...` inside the `omega`-large sets where all eighteen defects are
below `1/m` and `||X - I||_2 > c_0/2`. The resulting sequence satisfies condition 2.

The variant with another generator kept away from `I` is proved the same way. The only change is
which image is nontrivial. QED.
