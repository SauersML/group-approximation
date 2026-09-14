---
rg: 2
id: semidihedral-blocks-not-full-proof
kind: route
title: The twisted block unit evaluates to zero, transpose-inverse exchanges the blocks, and units span the Leavitt algebra
target: semidihedral-anti-central-blocks-are-not-full
requires:
  - anti-central-k0-states-can-be-chosen-transpose-invariant
artifacts:
  - research/artifacts/semidihedral-and-gl2-f3-blocks-forced-states-2026-09-12.md
---

Section 3 of the artifact, Proposition 3.1.
- `w + d = h`, so `pi(c_2) = -(I + h^2) = 0`. `alpha_*` exchanges `c_1` and `c_2` and fixes `H` pointwise.
- `pi` is onto because `R ~= M_2(R)` and every `2 x 2` matrix over a ring is a sum of four invertible matrices. Then
  `(pi, pi')(c_1 a + c_2 b) = (pi(a), pi'(b))`.
- If `eps_- = sum_k a_k c_1 b_k`, applying `pi'` gives `1 = 0`. Symmetrically for `c_2` with `pi`.
