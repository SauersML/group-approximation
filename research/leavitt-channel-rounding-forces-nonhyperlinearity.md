---
rg: 2
id: leavitt-channel-rounding-forces-nonhyperlinearity
kind: claim
title: Dimension-free rounding of near-idempotent bistochastic channels would make the binary Leavitt unit group nonhyperlinear
distinct_from:
  binary-leavitt-unit-group-hyperlinear: that is the open yes/no question; this is a proved conditional theorem whose premise, if established, answers it negatively.
  ucp-factorizations-round-to-matrix-expectations: that rounds channels supplied with a completely bounded UCP factorization; this consumes rounding under only the mixed infinity-to-2 idempotence defect that native heat maps actually satisfy.
  near-fixed-masas-round-channels-but-exclude-native-heat: that proves one special rounding class cannot contain native heat; this is the implication from the unrestricted rounding premise to nonhyperlinearity.
artifacts:
  - research/artifacts/leavitt-uniform-heat-rounding-alone-forces-nonhyperlinearity-2026-09-08.md
  - research/artifacts/leavitt-central-height-and-coordinate-swap-gap-2026-09-08.md
  - research/artifacts/leavitt-heat-kernel-inclusion-and-cp-reversal-obstruction-2026-09-08.md
  - research/artifacts/leavitt-poissonization-and-admissible-time-rounding-equivalence-2026-09-08.md
  - research/artifacts/leavitt-kazhdan-heat-rounding-boundary-and-factorial-center-countermodel-2026-09-08.md
---

**ESTABLISHED (conditional theorem).** Suppose there is a function
`f(delta) -> 0` as `delta -> 0`, independent of `d`, such that every
self-adjoint bistochastic UCP map `P:M_d -> M_d` with

```text
||P^2 - P||_(infinity->2) <= delta
```

has a unital subalgebra `A subset M_d` with `||P - E_A||_(infinity->2) <= f(delta)`.
Norms use the normalized trace. Then `H = L_(F_2)(1,2)^x` is not hyperlinear.

This records, as a graph node, the two-use argument written in the attached
September 8 artifacts, which had been cited only in the prose of
`binary-leavitt-unit-group-hyperlinear`.

- Canonical Kazhdan heat maps `exp(-t_n A_n)` of full canonical microstates,
  at admissible times `t_n -> infinity` with `epsilon_n t_n -> 0`, are
  self-adjoint bistochastic UCP maps with vanishing idempotence defect. So
  the premise gives the sequential rounding property `(R)` of the first
  artifact.
- **First use.** Rounding one global `H`-heat lets one select a canonical
  microstate sequence whose full external `H`-commutant in its matrix
  ultraproduct is scalar (component selection, Section 2 of the first
  artifact).
- **Second use.** Precompose with the isomorphism onto the native corner
  subgroup `L~=H` and round the native `L`-heat. The central-height lemma
  then produces a trace-zero element of norm at least `1/8` in the centre of
  the full `H`-commutant. It uses the one-sided inclusion of rounded
  algebras under the compressor `u`, together with the generation identity
  `H=<L,uKu^(-1)>`, Section 3 of the second artifact. This contradicts
  scalarity.

The artifacts also show that a positive answer to Alekseev--Thom Open
Problem 6.2(a) for every canonical embedding of `H` supplies `(R)`.

Scope: the premise is the open claim
`bistochastic-near-idempotents-round-dimension-free`. Neither branch of the
hyperlinearity question is decided by this node.

DERIVATION
leavitt-channel-rounding-forces-nonhyperlinearity-proof
