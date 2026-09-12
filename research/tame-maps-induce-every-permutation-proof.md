---
rg: 2
id: tame-maps-induce-every-permutation-proof
kind: route
title: Line cycles give 3-cycles with connected supports, hence the alternating group, and a scaling is odd
target: tame-maps-induce-every-permutation-of-prime-field-cubes
requires: []
artifacts:
  - research/artifacts/formalizability-prime-fields-and-alphabet-bridge-2026-09-12.md
---

Section 3 of the artifact.

- **Lemma 3.2.** Cycles `(u a_2 ...)` and `(u b_2 ...)` meeting only at `u` have commutator `(u a_2 b_2)`.
- **Lemma 3.3.** A group containing 3-cycles with connected supports contains the alternating group, by
  enlarging a maximal set `S` with `Alt(S)` inside the group. Case A adds one point by conjugation. Case B
  reduces to Case A through a commutator.
- **Proposition 3.1.**
  1. Line cycles `x_i -> x_i + delta_b` are `p`-cycles on axis lines.
  2. For `p = 2` they are hypercube-edge transpositions.
  3. For `p` odd and `n >= 2`, lines along two coordinates through a point meet once, giving the 3-cycles
     `(u, u + e_i, u + e_j)`, whose supports connect `F_p^n`.
  4. Scaling `x_1` by a generator of `F_p^x` is a product of `p^(n-1)` cycles of even length `p - 1`,
     hence odd.
  5. In one variable only affine maps are formally invertible.
