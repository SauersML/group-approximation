---
rg: 2
id: boundary-crossed-product-carries-leavitt-family-proof
kind: route
title: Three cylinder identities verify the Leavitt relations term by term
target: boundary-crossed-product-carries-leavitt-family
requires: []
artifacts:
  - research/artifacts/un-hyperlinear-paradox-2026-09-13.md
---

Complete direct proof, §1 of the artifact. In the crossed product `P_U u_g = u_g P_(g^(-1)U)`. For letters `c, c'`
of `F_d`:
- (I1) `c·C(c^(-1)) = ∂F_d \ C(c)`;
- (I2) `c·C(c') = C(cc') ⊆ C(c)` when `c' != c^(-1)`;
- (I3) the `2d` cylinders `C(c)` partition `∂F_d`.

Write `P^± = P_(C(c^(±1)))` for `c = c_i`.
- `t_i s_i = P^+ + 0 + 0 + P_(∂\C(c))(1-P^+) = 1`. The middle terms vanish by (I2) and disjointness; the last uses (I1).
- `s_i t_i = P^+ + 0 + 0 + P^- = P^+ + P^-`, by (I1) for `c^(-1)` and for `c`.
- For `i != j` with `e = c_j`, all four terms of `t_i s_j` vanish: disjoint cylinders, and
  `P_(C(ec)), P_(C(ec^(-1))) ≤ P_(C(e))` against `1 - P_(C(e))`, by (I2).
- `sum_i s_i t_i = sum_i (P_(C(c_i)) + P_(C(c_i^(-1)))) = 1`, by (I3).

The coefficients are never used.

Model tests: `d = 1` gives a unit (no paradox), and the Pestov ring admits no such family because its measure rank
function forces `rk(1) = d · rk(1)`.
