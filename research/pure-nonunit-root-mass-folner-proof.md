---
rg: 2
id: pure-nonunit-root-mass-folner-proof
kind: route
title: The compressor divides depth by d, so total-variation invariance caps each d-adic depth block
target: pure-nonunit-root-mass-is-log-scale-folner
requires:
  - compressor-transport-exactifies-under-vertex-rounding
artifacts:
  - research/artifacts/nh-unit-type-rounding-2026-09-12.md
---

Full derivation in §3 of the artifact.

- **Item 1.** `z^k B_n = A_u × z^k A_nu`, `z` is a unit on `A_u`, and `z` is nilpotent on `A_nu`.
- **Item 2.** `φ_A(z) = x^(A·1)` and `(A·1)_i = Σ_j A_ij >= d`, so `φ_A(z^k R_+) ⊆ z^(dk) R_+`.
- **Item 3.** Put `F_j = μ_n(depth <= d^j)`. By item 2, `D_A^(-1){depth <= d^j} ⊇ {depth <= d^(j+1)}`. The
  total-variation bound then gives `F_(j+1) <= μ_n(D_A^(-1){depth <= d^j}) <= F_j + η_n`.
- **Item 4.** `B_n` embeds in `∏_(i≠j) π_n(e_ij(R_+))`. Each factor is an elementary abelian p-subgroup of
  `U(n')`, of order at most `p^(n')`. So `dim_(F_p) A_nu <= r(r-1)n'`, which bounds finite depths,
  since `z^k A_nu` strictly decreases until it is `0`. Sum item 3 over the `1 + log_d(r(r-1)n')` blocks.
