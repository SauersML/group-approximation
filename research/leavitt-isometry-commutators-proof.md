---
rg: 2
id: leavitt-isometry-commutators-proof
kind: route
title: Commutator expansion of the Leavitt isometry relations under a rank model
target: leavitt-isometry-commutators-constrain-el3-rank-models
requires: []
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/leavitt-isometry-commutator-relations-2026-09-12.md
---

Direct computation. In `EL_3(R)`, `R = L_(F_2)(1,2)`, the Steinberg relation
`[x_12(a), x_23(b)] = x_13(ab)` holds for all `a, b in R`. Set `a = t_i`, `b = s_j`; the Leavitt
relation `t_i s_j = delta_ij` gives `[x_12(t_i), x_23(s_j)] = x_13(1)` for `i = j` and `= 1` for
`i != j`.

Apply the homomorphism `sigma` and write `A_i = sigma(x_12(t_i)) - 1`,
`B_j = sigma(x_23(s_j)) - 1`. In characteristic two each root element is an involution, so
`A_i^2 = B_j^2 = 0` and `sigma(x_12(t_i))^{-1} = 1 + A_i`, `sigma(x_23(s_j))^{-1} = 1 + B_j`.
Hence

```text
sigma([x_12(t_i), x_23(s_j)]) = (1+A_i)(1+B_j)(1+A_i)(1+B_j)
                              = 1 + A_iB_j + B_jA_i + A_iB_jA_i + B_jA_iB_j + A_iB_jA_iB_j ,
```

using `A_i^2 = B_j^2 = 0`. Equate with `sigma(x_13(delta_ij)) - `nothing`: for `i != j` the right
side is `1`, giving the vanishing identity; for `i = j` it is `1 + n_13(1)`, giving the second
identity with `Z = n_13(1)`.

The idempotent decomposition `1 + n_12(1) = (1 + n_12(e_0))(1 + n_12(e_1))` is the root-subgroup
homomorphism `(R,+) -> M^x` applied to `1 = e_0 + e_1`, `e_i = s_i t_i` (`e_0 + e_1 = s_0 t_0 +
s_1 t_1 = 1` in `R`, and `e_0, e_1` are orthogonal idempotents). No further input is used.

*Verified independently by `gk-vf-linear` (2026-09-12): Section 41 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`. Scope: the four relations are unavailable over finitely represented coefficient subrings jointly, not one at a time.*
