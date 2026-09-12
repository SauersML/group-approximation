---
rg: 2
id: shifted-root-pair-conjugates-to-idempotent-root-pair
kind: claim
title: The Leavitt-shifted root pair (x_12(t_0), x_23(s_0)) is simultaneously conjugate to (x_12(e_0), x_23(e_0)) and not to (x_12(1), x_23(1))
distinct_from:
  leavitt-rank-models-have-uniform-root-displacement: that proves displacement properties from conjugacy of single root elements; this classifies simultaneous conjugacy of a pair of root elements by the module type of the pair.
  leavitt-isometry-commutators-constrain-el3-rank-models: that records the operator identities forced by the commutator relation [x_12(t_i), x_23(s_j)] = x_13(delta_ij); this shows the shifted pair with commutator x_13(1) is not conjugate to the unit pair with the same commutator, so no conjugacy transports those identities to N_23 N_12.
artifacts:
  - research/artifacts/el3-two-root-identities-2026-09-12.md
---

Let `R = L_(F_2)(1,2)` and `e_0 = s_0 t_0`. In `GL_3(R) = EL_3(R)`:

1. There is `g` in `GL_3(R)` with `g x_12(e_0) g^-1 = x_12(t_0)` and `g x_23(e_0) g^-1 = x_23(s_0)`.
   For example

   ```text
   g = [ t_0        0                           0            ]
       [ s_1s_0t_1  s_0t_0 + s_1s_1s_0t_1       s_1s_1s_1t_1 ]
       [ 0          0                           t_0          ]
   ```

2. No element of `GL_3(R)` conjugates `(x_12(1), x_23(1))` to `(x_12(t_0), x_23(s_0))`, although
   both pairs have commutator `x_13(1)`.

For operators `N`, `M` on `R^3` put
`T(N, M) = (ker N ∩ ker M) / ((ker N ∩ ker M) ∩ (Im N + Im M))`. It is invariant under
simultaneous conjugation. `T = 0` for `(E_12, E_23)`, while `T ~= s_1 R` for
`(t_0 E_12, s_0 E_23)` and `T ~= R^3` for `(e_0 E_12, e_0 E_23)`. The pair has module type
`natural (x) R` in the first case and `(natural (x) R) (+) (trivial (x) R)` in the other two.

Consequence for rank models `sigma` of `EL_3(R)`: the only rank identity this gives is
`rk(n_23(s_0) n_12(t_0)) = rk(n_23(e_0) n_12(e_0))`. The pair gives no conjugacy-based handle
on `N_23 N_12`. Proof: `research/artifacts/el3-two-root-identities-2026-09-12.md`, Section 6.1.
