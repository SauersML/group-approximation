---
rg: 2
id: anti-central-swap-fullness-gives-projective-fullness
kind: route
title: Tensor the anti-central Cohn family through the block-diagonal map and absorb the Hadamard sector to invert the projective swap idempotent
target: projective-ternary-swap-idempotent-is-full
requires:
  - ternary-anti-invariant-swap-corner-is-full
  - ternary-leavitt-swap-problem-splits-at-central-involution
artifacts:
  - research/artifacts/anti-central-swap-fullness-gives-projective-2026-09-16.md
  - research/artifacts/invariant-output-descent-and-sensitivity-2026-09-12.md
---

## Why sufficient

Theorem 5 of the 2026-09-16 artifact. Let `c_- e_- b_- = eps_-` in `S_-`.

1. **Cohn family.** Part 2 of `ternary-leavitt-swap-problem-splits-at-central-involution` gives
   `[d] e_- [d] = eps_- - e_-`. With `[d]^2 = 1`, this gives `e_- [d] e_- = [d](eps_- - e_-) e_- = 0`. So `beta_1 = e_- b_-`, `beta_2 = [d] e_- b_-`, `gamma_1 = c_- e_-` and
   `gamma_2 = c_- e_- [d]` satisfy `gamma_i beta_j = delta_ij eps_-`.
2. **Tensor map.** `mu(g_1, g_2) = s0 g_1 t0 + s1 g_2 t1` is a group homomorphism `G x G -> G` with
   `mu(z,1) = zd`, `mu(1,z) = d` and `w mu(g_1,g_2) w = mu(g_2,g_1)`. Its linearization modulo `z` is a unital
   ring map `Psi : S_- (x) S_- -> f F_3[PG] f`, with `f = 2(1 - [dbar])`, and `[wbar] Psi(x (x) y) [wbar] = Psi(y (x) x)`.
3. **Images.** Put `X_i = Psi(beta_i (x) eps_-)`, `Y_i = Psi(gamma_i (x) eps_-)`, `X = Psi(beta_1 (x) beta_2)`
   and `Y = Psi(gamma_1 (x) gamma_2)`. Then `Y_i X_j = delta_ij f`, `YX = f`, and by the flip `Y [wbar] X = 0`.
4. **Witnesses.** Let `q_ab = 2(1 + a[wbar]) 2(1 + b[dbar])`, `e_w = 2(1 + [wbar])`, and `H = [hbar]` with
   `h = s0 t0 + s0 t1 + s1 t0 - s1 t1`, so that `h^2 = z` and `h w h^-1 = d`. Then

       b = q_++ + e_w X (X_1 H q_-+ + X_2),   c = q_++ + 2(q_-+ H Y_1 + Y_2) Y e_w

   satisfy `e_w b = b`, `c e_w = c` and `cb = 1`, hence `c ebar b = 1`.
5. **The two moves inside the proof.**
   - `2Y e_w X = Y(1 + [wbar])X = f` puts `f` below `q_+-`.
   - `H` carries `q_-+` onto `q_+-`, where the Cohn family absorbs it.
   - Every cross term dies by orthogonality of the `q_ab`.

Only the Leavitt relations and parts 1 and 2 of the splitting claim are used. The formulas were also checked
in an operator model by `experiments/ternary-swap-fullness-equivalence-2026-09-16/verify_identities.py`.
The converse is not known (Section 8.1 of the artifact).
