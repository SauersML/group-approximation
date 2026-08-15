---
rg: 2
id: compression-torsion-collapse-fourier-route
kind: route
title: Fourier idempotents reduce every finite order to the projection collapse
target: compression-torsion-collapse
requires:
  - corona-projection-collapse
artifacts:
  - GroupApproximation/Sofic/TorsionSpectralCollapse.lean
---

## Distinct from

- [[compression-torsion-collapse-assembly]] — That route proves the collapse analytically from scratch (rank cocycle, FH primitive, scaled transport) and is hypothesis-gated on its analytic inputs; this one derives the full finite-order case from the already-established projection collapse by explicit finite Fourier analysis, and is the route that is machine-checked.


## Why sufficient

Let `u = Theta(k)` be the represented witness, a unitary with
`u^m = 1`.  Its discrete Fourier idempotents

```text
p_j = m^{-1} sum_{t in Z/m} zeta^{-jt} u^t,   zeta = e^{2 pi i / m}
```

are self-adjoint idempotents (character orthogonality), and each is a
polynomial in `u`, so everything that commutes with `u` commutes with
every `p_j`.  Hence: the represented compressed copy centralizes each
`p_j`, and the `Theta(Lambda)`-conjugates of each `p_j` commute
pairwise because the conjugated witnesses do.  The projection collapse
(`corona-projection-collapse`) forces each `p_j` to commute with
`Theta(Lambda)`; Fourier reconstruction writes `u` as a
`zeta`-weighted sum of the `p_j`, so `u` itself commutes with
`Theta(Lambda)` and every collapse commutator dies.

No circularity: the projection collapse consumes only the ORDER-TWO
case of the collapse, which the involutive endpoint
(`involutive-collapse-formalized-proof`) establishes independently of
any projection statement; this route then returns every higher order.

This discharges, unconditionally and at every finite order, the
collapse gate of the globalization layer already kernel-checked in
`TorsionCompressionCollapse.lean`: the endpoints
`torsionCollapseDefect_le_actualCoronaMFResidual_of_kazhdan` and
`actualCoronaMFResidual_eq_torsionCollapseDefect_of_kazhdan` now hold
with no collapse hypothesis.  Main declarations in
`GroupApproximation/Sofic/TorsionSpectralCollapse.lean`:
`char_sum`, `fourierIdem_mul_self`, `star_fourierIdem`,
`fourierIdem_reconstruct`, `actualCoronaMFInvisible_of_torsionWitness`.
Authored in the 2026-08-15 generalization wave; the wave's closing
validation build certifies the kernel check.
