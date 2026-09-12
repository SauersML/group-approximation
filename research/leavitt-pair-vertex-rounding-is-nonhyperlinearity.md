---
rg: 2
id: leavitt-pair-vertex-rounding-is-nonhyperlinearity
kind: claim
title: Vertex rounding for the nine-leaf Leavitt pair is exactly nonhyperlinearity of the binary Leavitt unit group
distinct_from:
  hs-stable-vertex-rounding-for-every-model: that is the open rounding hypothesis (H1) for trace-preserving models of an infranormal Kazhdan pair; this instantiates it at the nine-leaf Leavitt pair, where it collapses to a statement about the unit group alone.
  leavitt-unit-hs-stable-iff-nonhyperlinear: that equates normalized-HS stability of the whole unit group with nonhyperlinearity; this equates rounding of trace-preserving models of the configuration group on its Kazhdan vertex with the same property.
  theorem-e-vertex-rounds-to-unit-type-representations: that is (H1) with unit-type targets at the Kun--Thom Theorem E pair, whose vertex has many finite images; this is the Leavitt pair, whose vertex has no nontrivial finite-dimensional unitary representation, so there the rounding premise has no arithmetic content.
artifacts:
  - research/artifacts/hyperlinear-nonsofic-l-times-2026-09-12.md
---

**ESTABLISHED.** Let `R = L_(F_2)(1,2)` and `Q = R^x`. Take the configuration of
`openai-nine-leaf-leavitt-configuration`:

```text
Gamma = EL_alpha(R) ~= EL_3(R)   <   G_L = EL_D(R) ~= EL_9(R)   <=   Q,
```

and a Kazhdan pair `(F, kappa)` for `Gamma`. Call a homomorphism
`sigma : G_L -> U(prod_U (M_n, tr_n))` *trace-preserving* if `tau(sigma(g)) = 0` for every
`g != 1`. The following are equivalent.

1. **(H1) at this pair.** For every trace-preserving `sigma`, with coordinates `sigma_n`, there
   are, after `o(n)` padding, genuine representations `pi_n : Gamma -> U(n')` with `n'/n -> 1` and
   `max_(s in F) ||sigma_n(s) - pi_n(s)||_2 -> 0` along `U`.
2. `G_L` is not hyperlinear.
3. `Q` is not hyperlinear.

## Proof

* **Both groups are the unit group.**
  - `GL_n(R) = EL_n(R)` for every `n >= 2` (`leavitt-gl-equals-el-and-perfect-unit-group`).
  - A complete prefix code with `k` leaves gives a ring isomorphism `M_k(R) ~= R`, so
    `EL_9(R) = GL_9(R) ~= Q`.
  - The code `alpha` partitions the cylinder `[0]`, so `Gamma ~= EL_3(e_0 R e_0) ~= EL_3(R) = GL_3(R) ~= Q`.
  - Hence `2 <=> 3`, and `Gamma` is minimally almost periodic
    (`binary-leavitt-unit-group-is-minimally-almost-periodic`).
* **3 => 1.** For unitaries, `||sigma(g) - 1||_2^2 = 2 - 2 Re tau(sigma(g))`. So a trace-preserving
  `sigma` puts every `g != 1` at distance `sqrt 2` from `1`, and it is an injective hyperlinear witness
  for `G_L`. If `G_L` is not hyperlinear there is no trace-preserving `sigma`, and 1 holds vacuously.
* **1 => 2.**
  1. Suppose `G_L` is hyperlinear. Then some embedding `sigma : G_L -> U(prod_U M_n)` has
     `tau o sigma` equal to the canonical trace, so `sigma` is trace-preserving.
  2. By 1 there are rounding representations `pi_n`. `Gamma` is minimally almost periodic, so every
     `pi_n` is trivial.
  3. `Gamma` is infinite, so the Kazhdan set `F` contains some `s != 1`.
  4. `o(n)` padding changes normalized distances by `o(1)`. So
     `||sigma_n(s) - 1||_2 -> 0` along `U`, while `||sigma(s) - 1||_2 = sqrt 2`. Contradiction.

No approximation property of any group is assumed.

## Consequences

* **Scope of the general hypothesis.** Read literally over every infranormal, non-normal Kazhdan pair,
  `hs-stable-vertex-rounding-for-every-model` contains condition 1. So its general form implies that
  `Q` is not hyperlinear, and a proof that `Q` is hyperlinear refutes it. Consumers should instantiate
  (H1) at the Theorem E pair, where the vertex has rich finite images.
* **The Kun--Thom mechanism has no internal Leavitt instance.** The unit-type projections of
  `unit-type-vertex-rounding-forces-compressor-commutant-rigidity` come from finite congruence images of
  the vertex. The Leavitt vertex has no nontrivial finite-dimensional unitary representation, so at this
  pair rounding is either vacuous or contradictory and carries no size. Transferring the Kun--Thom chain
  to `Q` needs an embedding instead (`kun-thom-wreath-embeds-in-leavitt-unit-group`).
* **Every hyperlinear model of `Q` is maximally unrounded.** If `Q` is hyperlinear, then on every nontrivial
  element of `Gamma` a trace-preserving model stays at distance `sqrt 2` from every genuine
  finite-dimensional representation.

Derivation: `leavitt-pair-vertex-rounding-nonhyperlinearity-proof`. No novelty is claimed. The
content is a scope correction for (H1) and a map of where the Kun--Thom chain can and cannot act.
