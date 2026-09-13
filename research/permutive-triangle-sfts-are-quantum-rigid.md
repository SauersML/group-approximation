---
rg: 2
id: permutive-triangle-sfts-are-quantum-rigid
kind: claim
title: A Z^2 SFT in which any two of x(z), x(z+e_1), x(z+e_2) determine the third is quantum rigid, and has a periodic point once a row or column is periodic
distinct_from:
  ledrappier-crossed-product-is-finitely-presented: that is one permutive shift over F_p, with a group law and roots of unity; this is the general permutive mechanism with no group law, and adds the periodicity constraint any aperiodic example must meet.
  sft-crossed-product-fp-iff-quantum-rigid: that characterizes finite presentation by rigidity; this is a sufficient local condition for rigidity.
artifacts:
  - research/artifacts/free-minimal-crossed-product-rings-and-permutive-rigidity-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `Ω ⊆ A^(Z^2)` be an SFT. Suppose each projection of the
occurring patterns on `T = {0, e_1, e_2}` onto two of its points is injective.

1. `Ω` is `D`-quantum rigid for every `D >= 1`. So `LC(Ω, k) ⋊ Z^2` is finitely presented over
   every field `k` (by `sft-crossed-product-fp-iff-quantum-rigid`).
2. If some point of `Ω` has a horizontally periodic row or a vertically periodic column, then `Ω`
   has a doubly periodic point.

**Mechanism.**
- **Determinism as operators.** Determinism on a triangle is an operator identity
  `E(z+e_2) ∈ alg(E(z), E(z+e_1))`, and likewise for the other two points. It needs only local
  commutation and admissibility.
- **Propagation.** Commutation at distance `k` in a row follows from distance `k - 1` in the row
  above and distances `k - 1`, `k - 2` in the row itself. This is Baumslag's lamp computation with
  no group law.
- **Periodicity.** Rows (columns) evolve by a sliding block code, so a periodic row returns and
  can be stacked into a doubly periodic point.

**Consequence.** A free triangle-permutive SFT, in any recoding, has row and column subshifts with
no periodic point, so both are non-sofic. This is the constraint that
`free-minimal-z2-sft-is-quantum-rigid` has to meet along this mechanism.

Route: `permutive-triangle-sfts-are-quantum-rigid-proof`.
