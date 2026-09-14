---
rg: 2
id: frobenius-support-idempotents-give-boolean-realization
kind: claim
title: For an isomorphism G_X → G_Y, the Frobenius sums S_V = I + Σ α(F21_V) are commuting idempotents; the corner group of V acts trivially off S_V iff S_V S_{X∖V} = 0, and orthogonality with no constant fixed vectors gives a Boolean algebra of supports commuting with α(L_X)
distinct_from:
  subshift-el3-isomorphisms-recognize-diagonals-up-to-normalizer: that is the full recognition up to the normalizer; this proves the idempotent-realization step under two vanishing hypotheses and an unconditional dichotomy, without concluding GL_3(B)
  subshift-elementary-group-rigid-supports-are-mutual-centralizers: that is the X-side support structure (mutual centralizers, normalizers); this transports it to idempotents in M_3(R_Y) through odd-order Frobenius subgroups
artifacts:
  - research/artifacts/sk-normalizer-recognition-2026-09-14-part1.md
---

Let `X, Y` be infinite minimal subshifts, `R = LC(·,F_2) ⋊ Z`, `G = EL_3(R)`, `M = R_Y^3`, and `α: G_X → G_Y` an
isomorphism. Let `F21 = C_7 ⋊ C_3 ≤ GL_3(F_2)`. For clopen `V`, let `F21_V` be its copy constant on `V`, let
`E3_V = E_3(e_VR_Xe_V)`, and put `S_V := I + Σ_{k∈α(F21_V)} k`. Then:

1. `S_V` is the idempotent onto `[M, α(F21_V)]` along `Fix(α(F21_V))`. On the X-side, `S_V = e_V I_3`. `S_V ≠ 0` for
   `V ≠ ∅`. `S_V` and `S_W` commute when `V ∩ W = ∅`. Every element of `G_Y` commuting with `α(F21_V)` commutes with
   `S_V`.
2. **(Dichotomy.)** For clopen `U ≠ ∅, X`, `α(E3_U)` acts trivially on `S_{X∖U}M` if and only if `S_US_{X∖U} = 0`.
3. **(Boolean realization.)** Assume:
   - (O) `S_VS_W = 0` for disjoint `V, W`;
   - (O′) `S_X = I`.

   Then `V ↦ S_V` is an injective unital Boolean algebra homomorphism into commuting idempotents of `M_3(R_Y)`, and
   `α(E3_V) ≤ I + S_VM_3(R_Y)S_V`. So `α(L_X)` centralizes `𝔅 = span{S_V} ≅ LC(X,F_2)`.

For `α = inn(diag(u,1,1))`, `S_V = diag(e_{TV}, e_V, e_V)` is not scalar, and (O), (O′) hold.

Status: proved in `frobenius-support-idempotents-boolean-realization-proof`, unreviewed. Item 2(⇐) imports that the
corner ring of `U` is the crossed product of the induced system, so `E3_U` is simple.
