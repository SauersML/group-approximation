---
rg: 2
id: weakly-finite-leavitt-defect-triviality-proof
kind: route
title: Matrix units give a unital corner map from the Leavitt algebra, and weak finiteness of the corner kills it
target: weakly-finite-leavitt-representations-killing-defect-are-trivial
requires:
  - leavitt-gl-equals-el-and-perfect-unit-group
  - reversed-root-pair-identity-forces-root-squares-to-vanish
  - el3-unit-root-matrix-units-iff-two-root-identities
  - matrix-unit-rank-models-extract-ring-rank-models
artifacts:
  - research/artifacts/weakly-finite-representations-of-ternary-leavitt-units-2026-09-12.md
  - research/artifacts/sylvester-rank-function-two-root-gate-2026-09-12.md
---

Artifact Section 2, Theorem 2. Steps 1, 2, 3 and 5 are the ring-algebra steps of
`research/artifacts/sylvester-rank-function-two-root-gate-2026-09-12.md` Theorem 1, whose arbitrary-ring
scope `w3-vf-linear` passed (its Section 23). Only step 4 differs.

1. **Squares.** `N_23 N_12 = 0` gives `N_ab^2 = 0` for every root, by Weyl spread and the commutator formula.
2. **Matrix units.** [TRI] Theorem A, for any unital ring, gives orthogonal idempotents `p_i` and matrix
   units `u_ij in p_i W p_j` with `rho(x_ij(1)) = 1 + u_ij`.
3. **Corner map.** From `matrix-unit-rank-models-extract-ring-rank-models` only the ring algebra is used:
   [RR] Proposition 6 (`p = 2`), or Proposition 8 with Corollary 9 (`p` odd). It gives a unital ring
   homomorphism `C : R -> p_1 W p_1`.
4. **Weak finiteness kills the corner.**
   - If `xy = p_1 I_n` over `p_1 W p_1`, then `(x + (1-p_1)I)(y + (1-p_1)I) = I`, so `yx = p_1 I_n`. Corners
     of weakly finite rings are weakly finite.
   - `C(t_0) C(s_0) = p_1` gives `C(s_0) C(t_0) = p_1`, so `C(s_1 t_1) = 0`.
   - Then `p_1 = C(t_1 (s_1 t_1) s_1) = 0`.
5. **Triviality.** `u_ij = u_i1 u_1j = 0`, so every `x_ij(1)` dies. `ker rho` then contains every
   `x_ij(a) = [x_ik(a), x_kj(1)]`, hence `EL_3(R) = Γ`. QED

*Verification by `w4-vf-linear-b` (2026-09-12), Section 36.2 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`: PASS for steps 4–5. Re-derived: the corner padding, `C(s_1 t_1) = 0`, `p_1 = C(t_1)C(s_1 t_1)C(s_1) = 0`, and the normal closure of the root elements. Steps 1–3 cite the reversed-root identity, `[TRI]` Theorem A and the ring-algebra forms of `[RR]` Propositions 6/8 and Corollary 9 (passed by `w3-vf-linear`, Section 23). They were not re-derived here.*
