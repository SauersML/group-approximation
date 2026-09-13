---
rg: 2
id: periodic-quantum-tilings-refute-quantum-rigidity
kind: claim
title: A periodic operator-valued tiling of an aperiodic SFT refutes quantum rigidity at its scale, and has no one-dimensional, or for wall-rigid shifts two-dimensional, composition factor
distinct_from:
  sfts-without-finite-orbits-are-not-residually-finite-actions: that rules out classical finite models of an aperiodic SFT action; this concerns operator-valued periodic tilings, which need no periodic point and refute finite presentation of the crossed product when they exist.
  sft-wall-rigidity-iff-idempotent-commutator-ideal: that characterizes the first-order obstruction on the plane; this identifies finite-dimensional modules of the local presentation with periodic quantum tilings and records that they must be contextual.
artifacts:
  - research/artifacts/quantum-rigidity-walls-and-commutator-ideal-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `Ω ⊆ A^(Z^2)` be an SFT with no periodic point, `D >= r`, and `k` a field.
Let `A_D = C_D ⋊ Z^2` be the local presentation of `sft-crossed-product-fp-iff-quantum-rigid`, and `V != 0` a
finite-dimensional `A_D`-module.

1. **Noncommutation.** The family `P_z^a` on `V` does not commute, and `V` has no one-dimensional
   `C_D`-composition factor. Hence `Ω` is not `D`-quantum rigid. Equivalently, if `Ω` is `D`-rigid, then
   `A_D` has no nonzero finite-dimensional module.
2. **Periodic families.** Over a finite field, nonzero finite-dimensional `A_D`-modules are the same as
   periodic families, called *periodic quantum tilings*. These are idempotent partitions `E_a(z)` on a
   finite-dimensional space, locally commuting and locally admissible, with `E(z + λ) = E(z)` for all `λ` in
   a finite-index subgroup `Λ` of `Z^2`.
3. **Wall-rigid shifts.** Over an algebraically closed field, if `Ω` is `D`-wall-rigid
   (`sft-wall-rigidity-iff-idempotent-commutator-ideal`), then `V` has a composition factor of dimension
   `>= 3` carrying a noncommuting family.

**Mechanism.**
- A one-dimensional composition factor is a character of the image of `C_D`. It reads off a legal
  configuration.
- The finitely many maximal ideals of that finite-dimensional image are permuted by `Z^2`, so the
  configuration has a finite-index stabilizer and is periodic.

**Use.** A periodic quantum tiling of Labbé's tiles, at every scale `D`, would refute
`labbe-wang-shift-crossed-product-is-finitely-presented`. It would have to be genuinely contextual, with no
classical and no two-dimensional pieces.

Route: `periodic-quantum-tilings-refute-quantum-rigidity-proof`.
