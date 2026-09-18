# Referee report (gq-referee-a, proof-gap lens): (Q,+) in a finitely generated subgroup of U(L_Z(1,2))

**Reviewed:** `integral-leavitt-unit-group-contains-q` and route `-proof` (lane gq-deep-ring-1,
c71dd8fe4, cross-references 731542306), read on origin/main.

**Verdict: PASS.** No gaps found. This is a sub-lemma, not the root.

## Steps
- **Step 1.** Correct.
  - For pairwise incomparable `g_a` we have `y_{g_b} x_{g_c} = δ_bc`. So `E_ab E_cd = δ_bc E_ad`, and
    `M ↦ Σ M_ab E_ab` is a ring map `M_r(Z) → e_Γ L e_Γ`.
  - It is injective by `E_1a(·)E_b1 = M_ab E_11`, `E_11 ≠ 0`, and the fact that `L_Z(1,2)` is a free
    `Z`-module (normal-form basis).
  - `u(Γ,M) = (1-e_Γ) + φ(M)` is multiplicative because `(1-e)φ(M) = 0 = φ(M)(1-e)`.
- **Step 2 (refinement, `j` outer).** Correct.
  - `x_{g_a} y_{g_b} = x_{g_a}(Σ_j x_{w_j} y_{w_j}) y_{g_b} = Σ_j x_{g_a w_j} y_{g_b w_j}`, since `y` is
    read in reverse.
  - So `Σ_{ab} M_ab E_ab = Σ_j Σ_{ab} M_ab E'_{(j,a),(j,b)}`, which is `I_s ⊗ M` with `j` as the block
    index. That matches the block structure of `T_{k+1}`, where the `k+1` blocks are indexed by `j`.
- **Step 3 (V-transitivity on proper configurations).** Correct.
  - `v_g x_{e_i w} = x_{d_i w}`, because `(e_i)` is a prefix code, so only `i' = i` contributes.
  - Dually `y_{e_i w} v_g^{-1} = y_{d_i w}`. Refining `g`'s code makes every `g_a` extend some `e_i`.
  - For two proper configurations of the same size, the complements are finite unions of cones that
    can be split to equal counts. This is exactly why nonempty complements are needed.
  - `u(Γ,P)` is the permutation unit of the cone permutation, because
    `Σ_l x_{c_l} y_{c_l} = 1 - e_Γ` over the complement code.
- **Step 4 (the roots).** Correct.
  - `(ΠD)^{k+1} = ∏_{i=1}^{k+1} (Π^i D Π^{-i}) · Π^{k+1} = I_{k+1} ⊗ T_k`. Each conjugate places
    `T_k` in a different block, and `Π^{k+1} = I`.
  - `|Γ_{k+1}| = (k+1)|Γ_k| = r_{k+1}`. Every word begins with `0`, so the cone `1` stays in the
    complement.
  - `a_1 = 1 - e + E_11 + E_21 + E_22 = 1 + x_{01} y_{00} = t`.
- **Step 5 (injectivity).** Correct.
  - `a_{k'}^{k'!/k!} = a_k` gives a well-defined homomorphism `Q → U(L)`.
  - `(x_{01}y_{00})^2 = 0`, so `t^m = 1 + m x_{01} y_{00}`, which is not `1` for `m ≠ 0` by
    torsion-freeness.
  - So the kernel meets `Z` trivially, and a nonzero subgroup of `Q` always meets `Z`.
- **Step 6 (finite generation).** Correct.
  - `a_{k+1} = u(Γ_{k+1}, Π) · u(Γ_{k+1}, D)`. The first factor is in `V`.
  - The second is `u(Γ^0_{k+1}, T_k)`, since the identity blocks cancel against `-e`. It is
    `V`-conjugate to `a_k` by Step 3, since both configurations have size `r_k` and are proper.
- **Step 7.** Correct. `L → A ⊗ L` is injective for `A` of characteristic 0, because `L` is free over
  `Z`.

## Consequences
- **`GL_r(Z)`.** Correct. `u(Γ, e_ab(1)) = 1 + x_{g_a} y_{g_b}` is `V`-conjugate to `t` for proper `Γ`.
  Elementary matrices together with one transposition matrix generate `GL_r(Z)`.
- **Distortion.** Correct: distortion is inherited by finitely generated overgroups.
- **`t` is not conjugate to `t^p` (cokernel argument).** Correct.
  - `L` acts faithfully on `M = LC(C,Z)`: it acts nonzero on `LC(C,Q)`, `L_Q(1,2)` is simple, and
    `LC(C,Q) = Q ⊗ M`.
  - `x_{01} y_{00}` maps `M` onto the direct summand of functions supported on the cone `01`. So
    `M/(t-1)M` is free.
  - `(t^p - 1)M = p·(summand)`, so that cokernel has `Z/p`-torsion.
  - Conjugation in `U(L) ≤ Aut(M)` preserves these cokernels. So no element of `U(L)` normalizes this
    copy of `Q` by multiplication by `p`.
  - This rules out extending *this copy* to `Aff(Q)` by conjugation. It says nothing about other copies.

## Remarks
- **The host claims are only non-exclusion.** The statement that `<V, t>` passes O1–O4 means only that
  those obstructions do not exclude it. No finite presentation or simplicity is claimed, and none is
  proved.
- **Relation to Belk–Hyde–Matucci.** The analogy is apt: roots come from splitting into commuting
  refined copies and rotating them, as in the `T̄` construction.
