---
rg: 2
id: corner-rank-no-contraction-proof
kind: route
title: Combine the defect factorization at the shifted pair with idempotent displacement constancy and level transpositions
target: corner-rank-data-cannot-contract-the-two-root-deviation
requires:
  - el3-two-root-violation-splits-over-leavitt-branches
  - leavitt-rank-models-have-uniform-root-displacement
  - leavitt-gl-equals-el-and-perfect-unit-group
artifacts:
  - research/artifacts/w3-vf-linear-verification-2026-09-12.md
  - research/artifacts/corner-rank-contraction-obstruction-2026-09-12.md
---

## Why sufficient

* **Part 1.** Corollary 1.1 of `el3-two-root-violation-splits-over-leavitt-branches` states
  `rk(n_ik(ab) - n_ij(a) n_jk(b)) = rk(n_jk(b) n_ij(a))` in a rank ultraproduct, since `1 + n_ij(a)`
  and `1 + n_jk(b)` are units there. Apply it with `(i, j, k) = (1, 2, 3)`, `a = t_0`, `b = s_0`, and
  `t_0 s_0 = 1`. Part 1 of `leavitt-rank-models-have-uniform-root-displacement` gives
  `rk(n_13(1)) = rho(1) = rho`, and subadditivity of rank in both directions gives the two
  inequalities.
* **Part 2.** Part 4 of `leavitt-rank-models-have-uniform-root-displacement` gives `rho(e) = rho` for
  every nonzero idempotent `e`, and part 1 transports it from the `12` root subgroup to `13`. Every
  `e_gamma` is a nonzero idempotent.
* **Part 3.** For `|gamma| = |gamma'| = k`, the element
  `w = s_gamma t_gamma' + s_gamma' t_gamma + sum_mu s_mu t_mu`, summing over the other words of
  length `k`, satisfies `w^2 = sum_{|mu| = k} e_mu = 1` by the Cuntz relation, so `w` is a unit of
  `R` and `W = diag(w, w, w)` lies in `GL_3(R)`, which equals `EL_3(R)` by
  `leavitt-gl-equals-el-and-perfect-unit-group`. Then `W x_ab(c) W^-1 = x_ab(w c w)` and
  `w e_gamma w = e_gamma'`, so conjugation by `sigma(W)` carries `P_gamma` to `P_gamma'`, and
  conjugation by a unit preserves rank.

## Scope

The consequence paragraph of the claim quotes the refutation of branch-rank additivity from
`rank-modelled-coefficients-violate-two-root-identities` without re-deriving it, and that node is
not a prerequisite of the three parts proved here.

*Verification by `w3-vf-linear` (2026-09-12), Section 16.1 of `research/artifacts/w3-vf-linear-verification-2026-09-12.md`: PASS for parts 1–3. Part 1 was derived directly as n_13 − XY = −(1+X)YX V'^-1; part 4 of the displacement claim covers single idempotents. Precision remark on the claim's consequence paragraph: the cited calibration satisfies Σ_γ rk P_γ = 2^(1−k)/9 <= 1, so it refutes orthogonality of the root branch defects a_γ, b_γ, not the displayed branch-rank inequality.*
