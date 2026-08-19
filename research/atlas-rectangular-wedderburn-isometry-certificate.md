---
rg: 2
id: atlas-rectangular-wedderburn-isometry-certificate
kind: claim
title: Finite-multiplicity atlas extraction forces a rectangular isometry between unequal Fourier corners
distinct_from:
  atlas-one-cut-finite-multiplicity-extraction: that asks for a unitary with asymmetric leakage inside one finite multiplicity algebra; this target allows two different fixed Wedderburn corners and asks only for one Gram relation on one rectangular block.
  pauli-compressor-equalizer-density-decays: that rules out a positive-density compressor-invariant equalizer fiber; this target transports between unequal fixed Fourier multiplicity corners and does not require a common equalizer sector across depths.
  universal-atlas-ideal-cannot-force-hall-deficit: that rules out a universal relator-ideal proof of the required finite-trace mismatch; this target is explicitly allowed to depend on finite external multiplicity data.
---

In the canonical regular-`A_8` relative-unitary model from
`leavitt-regular-atlas-hyperlinearity-criterion`, there are irreducibles
`sigma,tau` with `d_sigma<d_tau` and, for each finite external multiplicity
`k`, a **coordinate-extracted** rectangular operator

```text
X_k : p_tau H_k -> p_sigma H_k
```

such that the atlas packet defect `delta_k` controls

```text
||p_tau-X_k^* X_k||_2 <= C delta_k^c,                (ARW1)
```

with constants independent of `k`.  The extraction may use the finite
multiplicity decomposition, singular-value/rank selection, and a fixed finite
matrix amplification, but it must be canonical enough that the estimate is
uniform along a microstate sequence.

The unequal regular multiplicities make `(ARW1)` impossible as
`delta_k -> 0`: `rectangular-wedderburn-block-isometry-gap` supplies the fixed
rank floor.

## What the factor-model audit changes

The earlier version proposed a stronger machine-searchable target in which a
fixed star-polynomial `X(U)` had
`p_tau-X(U)^*X(U)` in the universal two-sided relator ideal.  That route is
impossible.  Such a universal identity would hold for the internal exact
relative chart unitary in the Leavitt group factor
(`leavitt-factor-regular-charts-inner-conjugate`).  Since `X(U)` is typed from
the larger-trace corner to the smaller one, the resulting exact isometry
would violate finite-factor trace monotonicity.  This is the singleton form
of `universal-atlas-ideal-cannot-force-hall-deficit`.

Therefore the operator `X_k` in the live claim cannot be one fixed universal
star-polynomial coefficient expression whose Gram defect is an algebraic
relator consequence.  The **selection of the finite coefficient shadow is
the theorem**.  This is precisely the distinction between finite external
multiplicity and the infinite-multiplicity exact factor model.

## Attempts

- **Use ideal compilation only upstream of selection.** Exact coefficient
  consequences can constrain finite block matrices, but the final rectangular
  arrow has to be selected from their finite-dimensional singular/rank data;
  it cannot itself be a universal ideal consequence.
- **Start with interior information.** Boundary-only exact models are already
  known. Include the canonical interior packet; collision `19243` is a useful
  discriminator only after proper child/multiplicity refinement, since
  `Collision19243.lean` proves the parent-block identity for an arbitrary
  characteristic-two involution.
- **Prefer degree imbalance over invariant fibers.** The
  `pauli-compressor-equalizer-density-decays` no-go explains why iterating one
  fixed equalizer character loses density.  A finite-coordinate rectangular
  selection can instead aggregate the positive-density singular directions
  across several Fourier corners before choosing the unequal source/target
  pair.
- **Falsification.** Any exact finite regular-margin solution of the selected
  boundary-plus-interior packet refutes a proposed extraction rule.  Replay
  candidates on all archived finite atlas countermodels before promoting the
  selection to a route.