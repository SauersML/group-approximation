---
rg: 2
id: positive-entropy-sft-crossed-products-are-not-fp
kind: claim
title: A Z^2 subshift of finite type with positive entropy has an infinitely presented crossed-product algebra
distinct_from:
  sft-crossed-product-fp-iff-quantum-rigid: that is the characterization by quantum rigidity; this is the entropy criterion that refutes rigidity at every scale.
  minimal-subshift-crossed-product-is-not-finitely-presented: that treats minimal Z-subshifts through LEF; this treats two-dimensional SFTs, periodic or not, through walls of agreement.
---

**ESTABLISHED (unreviewed).** Let `k` be a field and `Ω ⊆ A^(Z^2)` an SFT with `h_top(Ω) > 0`.
Then `LC(Ω, k) ⋊ Z^2` is not finitely presented.

**Mechanism.** Take an ergodic measure of positive entropy. Pigeonhole on box patterns gives an
annulus pattern of width `> 2D` with two different fillings. Poincaré recurrence gives two far
apart occurrences of it in one configuration. Rewriting both boxes gives two configurations that
agree on a wall and differ on both sides of it. That refutes `D`-rigidity with `W = k^2`, for every
`D`.

**Consequences.**
- **For the ring route.** Any Z^2-SFT coefficient algebra must have zero entropy.
- **For Labbé's shift.** `Ω_U` is minimal and self-similar, so it has zero entropy. For a minimal
  SFT, a wall certificate with a finite side already forces positive entropy
  (artifact, Proposition 4). So every certificate against `Ω_U` has two infinite sides.

Route: `positive-entropy-sft-crossed-products-are-not-fp-proof`.
