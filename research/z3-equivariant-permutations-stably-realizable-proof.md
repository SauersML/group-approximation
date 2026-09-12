---
rg: 2
id: z3-equivariant-permutations-stably-realizable-proof
kind: route
title: Commutators of line-controlled level flips with level-controlled SL_2(F_4) shears give every level-dependent rotation
target: z3-equivariant-permutations-are-stably-realizable
requires:
  - finite-group-formalizability-equals-equivariant-automorphism
artifacts:
  - research/artifacts/z3-rotation-stable-realization-2026-09-12.md
  - research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md
---

Artifact Sections 0–2.
1. **Coordinates.** Each track splits as `s_i` plus `v_i in V`, and `V^2 = F_4^2`, where `F_4 = F_2[R]`
   acts by matrices commuting with the shift. Boolean points are `(s_1, s_2, u_1, u_2)` with
   `u -> omega u` under the shift.
2. **Moves.**
   - Level-controlled elementary shears `e(s_1 c)` realize `A in SL_2(F_4) = E_2(F_4)` at level
     `s_1 = 1`, and the identity at `s_1 = 0`.
   - Averaging a Boolean interpolant over `Z_3` realizes every invariant control function in a flip
     `s_1 -> s_1 + p(v)`.
3. **Lemma 1.** For a line `l` and `A` fixing `l` with eigenvalue `omega`, the commutator of the flip
   controlled by `l` with `Y_A` rotates `l` by `omega^2` at `s_1 = 1`, by `omega` at `s_1 = 0`, and fixes
   everything else. The four cases are checked directly, using that `A` preserves `l` and its
   complement.
4. **Theorem 2.** Put `Q = R o (prod_l C_l)^-1`. Then `Y_(diag(omega^2, omega)) o Q` has shadow
   `u_1 -> omega^(s_1) u_1`, which fixes `s_1`, `s_2` and `u_2`. That is `rho x id`.
5. **Corollary 3.** `K x id` is realized by `G_tri x id`. `K` has index 3 in the order-36 group, and no
   subgroup has order 24, so `<K, rho>` is all of it.
6. **Formalizability.** The stable form of `finite-group-formalizability-equals-equivariant-automorphism`
   converts each realization into a stable formalization.

**Verification (w3-vf-nonlinear, 2026-09-12): PASS.** Re-derived independently: averaging restricts to
`3f = f`; the four cases of Lemma 1; `Q` acts by `omega^2` at level 1 and by `1` at level 0; `diag(omega^2, omega)
omega^2 = diag(omega, 1)`; the identification with `rho x id` via `u(Rx) = omega u(x)`; and index 3 in a group of
order 36 (`research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md`, Section 12).
