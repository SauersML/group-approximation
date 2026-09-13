---
rg: 2
id: laurent-sl3-central-covers-never-witness-instability-proof
kind: route
title: Harder's vanishing plus transfer makes H^2(Delta;Q) zero, so a torsion-free central kernel would split off a map to Q and contradict property (T)
target: laurent-sl3-central-covers-never-witness-instability
requires:
  - harder-function-field-s-arithmetic-cohomology-vanishing
  - function-field-hecke-pair-is-perfect-codense-kazhdan
  - kazhdan-cover-models-round-iff-kernel-fixed-mass-one
  - finite-multiplier-projective-models-round-strictly
---

Notation as in the claim.

## 1. Cohomology

- **Vanishing.** `A(f)` is a congruence subgroup of `SL_3(O_S)`, `S = {0,∞}`, `r|S| = 4`. By
  `harder-function-field-s-arithmetic-cohomology-vanishing`, `H^ν(A(f);Q) = 0` for `ν = 1,2,3`.
  `A(f)` has finite index in `Δ`, so restriction `H^ν(Δ;Q) -> H^ν(A(f);Q)` is injective (transfer),
  and `H^ν(Δ;Q) = 0` for `ν = 1,2,3`.
- **Integral groups.** `A = EL_3(F_q[t,1/t])` has (T) (item 1 of
  `function-field-hecke-pair-is-perfect-codense-kazhdan`), and so does `Δ`. So `H_1(Δ;Z)` is finite.
  - Since `Q` is injective, universal coefficients give `H^2(Δ;Q) = Hom(H_2(Δ;Z),Q)`. This vanishes,
    so `H_2(Δ;Z)` is torsion.
  - Therefore `Hom(H_2(Δ;Z),Z) = 0`, and `H^2(Δ;Z) ≅ Ext(H_1(Δ;Z),Z)`, which is finite.

## 2. Central covers

- **Setup.** Let `N_t` be the torsion subgroup of `N` and `V = N/N_t`. Suppose `V ≠ 0`. Then
  `V ⊗ Q ≠ 0` and `V` embeds in `V ⊗ Q`, so there is a homomorphism `φ : V -> Q` that is nonzero.
- **Pushout.** `1 -> V -> Δ~/N_t -> Δ -> 1` is a central extension. Push it out along `φ` to a
  central extension `1 -> Q -> E -> Δ -> 1`.
  - Its class lies in `H^2(Δ;Q) = 0`, so it splits.
  - A split central extension is a direct product: `E ≅ Q × Δ`.
- **Contradiction.** The composite `Δ~ -> Δ~/N_t -> E -> Q` is a homomorphism. On `N` it restricts
  to `φ` composed with `N -> V`, which is nonzero. So `Δ~` has infinite abelianization, which
  contradicts (T). Hence `V = 0`, and `N` is torsion.
- **Finiteness under (FP).** A surjection from a finitely generated group onto a finitely
  presented group has a finitely normally generated kernel. `N` is central, so its normal closure
  is the subgroup it generates, and `N` is a finitely generated torsion abelian group, hence
  finite.

## 3. Rounding

- **Pulled-back models.** Let `ρ_k` satisfy (KC1) with `N` finite. From
  `||ρ_k(n) - 1||_2^2 = 2 - 2 Re tr ρ_k(n)` and `|tr ρ_k(n)| <= 1` we get `tr ρ_k(n) -> 1` for each
  `n ∈ N`. The projection onto `Fix_N(ρ_k)` is `E_k = |N|^(-1) Σ_(n∈N) ρ_k(n)`, so
  `tr E_k -> 1`. This is condition (c) of `kazhdan-cover-models-round-iff-kernel-fixed-mass-one`,
  which gives strict rounding.
- **Projective models.** `Δ` is finitely generated. `H_1(Δ;Z)` is finite by §1. `H_2(Δ;Z)` is
  torsion by §1 and finitely generated under (FP), hence finite. So
  `finite-multiplier-projective-models-round-strictly` applies.
- **Dogon 1.3.** Let `1 -> B -> G -> Δ -> 1` be central with `B` torsion-free and nonzero. §2,
  with `N = B`, shows that `G` is not Kazhdan; its proof produces a nonzero homomorphism `G -> Q`.
