---
rg: 2
id: fiber-type-toric-arrangement-groups-lie-in-the-pbh-class-proof
kind: route
title: Induct up the Bibby--Delucchi tower, applying the free-kernel permanence at each bundle whose punctured-G fibre has free fundamental group of rank at least 2
target: fiber-type-toric-arrangement-groups-lie-in-the-pbh-class
requires:
  - free-kernel-extensions-stay-in-the-permutational-class
  - boone-higman-type-a-class-closed-under-finite-extensions
  - type-a-action-gives-boone-higman-for-subgroups
---

**Input** (Bibby--Delucchi, arXiv:2202.11996v2, read from the PDF).
- **Definition 3.4.1.** `A ⊂ Γ` is fiber-type if `rk Γ = 1`, or if there is a rank-one
  split direct summand `Γ' ⊆ Γ` and a fiber-type `B ⊂ Γ/Γ'` such that the projection
  `p: Hom(Γ, G) -> Hom(Γ/Γ', G)` restricts to a fibration `M(A) -> M(B)` whose fibres
  are `G` with finitely many points removed.
- **Theorem 3.4.3.** For essential `A`, fiber-type ⟺ `P(A)` supersolvable.

No other input from that paper is used. In particular their Corollary 3.4.4
(asphericity) is re-derived in step 2 below.

We prove, by induction on `rk Γ`: for every fiber-type `A`, `M(A)` is aspherical and
`π_1(M(A)) ∈ B_A`. Essentiality is not needed.

**Step 1 (rank one).** `M(A)` is `G` minus `ℓ >= 0` points. It is aspherical, and
`π_1` is:
- free of rank `ℓ + 1` in the toric case (`C^×` minus `ℓ` points is `C` minus `ℓ + 1`);
- `Z^2` (for `ℓ = 0`) or free of rank `ℓ + 1` (for `ℓ >= 1`) in the elliptic case.

Every finitely generated free group embeds in `F_2 ≅ Inn(F_2) ≤ Aut(F_2) ∈ B_A`, and
`Z^2 = Z × Z ∈ B_A` by closure under subgroups and products
(`aut-free-groups-satisfy-permutational-boone-higman`,
`boone-higman-type-a-class-closed-under-finite-extensions`).

**Step 2 (the bundle).** Let `p: M(A) -> M(B)` be the fibration of Definition 3.4.1,
with fibre `F = G − {ℓ points}`. By induction `M(B)` is aspherical and
`π_1(M(B)) ∈ B_A`.
- *Asphericity.* `F` is aspherical: a punctured surface, `C^×`, or `E`. The long exact
  sequence gives `π_i(M(A)) = 0` for `i >= 2`.
- *Case `ℓ >= 1`.* `π_1(F)` is free of rank `ℓ + 1 >= 2`, and `π_2(M(B)) = 0`. Part 4
  of `free-kernel-extensions-stay-in-the-permutational-class` gives
  `π_1(M(A)) ∈ B_A`.
- *Case `ℓ = 0`.* Bibby--Delucchi's Lemma 3.2.1 counts `(t + Y) ∩ H_α` as `c(α)^d`
  points for `α ∉ A_Y`. So `ℓ = Σ_(α ∉ A_Y) c(α)^d = 0` forces `A = A_Y ⊆ Γ''`, where
  `Γ = Γ' ⊕ Γ''`.
  - Then `T = Hom(Γ', G) × Hom(Γ'', G)`, the arrangement only constrains the second
    factor, and `M(A) ≅ G × M(B)`.
  - So `π_1(M(A)) = π_1(G) × π_1(M(B))`, with `π_1(G) ∈ {Z, Z^2}`.
  - It lies in `B_A` by closure under products.

**Step 3 (envelope).** `π_1(M(A))` is finitely generated. In the toric case `M(A)` is a smooth affine variety. In the elliptic case it is a compact complex torus minus finitely many closed submanifolds. Either way it has the homotopy type of a finite CW complex.
Every finitely generated group in `B_A` embeds in a finitely presented simple group
and has solvable word problem (`type-a-action-gives-boone-higman-for-subgroups`). ∎

**The C_n example.** Take `Γ = Z^n` and `A = {2e_i, e_i ± e_j}`, so
`M(A) = {v ∈ (C^×)^n : v_i^2 ≠ 1, v_i ≠ v_j^(±1)}`. Take `Γ' = Z e_n`, so that `p`
forgets `v_n`.
- The fibre over `(v_1..v_(n-1))` is `C^×` minus `{±1} ∪ {v_i^(±1) : i < n}`.
- These `2n` points are distinct, because `v_i^2 ≠ 1` and `v_i ≠ v_j^(±1)`. So the
  count is constant.
- By their Lemma 3.2.4 ((3) ⟺ (4)) and Theorem 3.3.1, `p` is a fibration.
- The base is the `C_(n-1)` arrangement. By induction `A` is fiber-type.
