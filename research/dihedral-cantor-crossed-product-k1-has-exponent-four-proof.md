---
rg: 2
id: dihedral-cantor-crossed-product-k1-has-exponent-four-proof
kind: route
title: Restriction of scalars along the rotation subring, then induction, is multiplication by 2 over F_2 because the multiplication kernel is an inner-twisted bimodule; the reflection inverts the generator of K_1 = Z
target: dihedral-cantor-crossed-product-k1-has-exponent-four
requires:
  - binary-subshift-ring-k1-is-half-orbit-index
artifacts:
  - research/artifacts/dihedral-cantor-k1-exponent-four-2026-09-16.md
---

Conventions: row vectors, `K_1 = GL/E`. Facts used: (K-a) conjugation invariance, (K-b) additivity on short exact
sequences of finitely generated free modules (block triangular matrices), (K-c) `K_1(M_n A) = K_1(A)`. Artifact §0.

- **Step 1 (restriction of scalars).** `A = A′ ⊕ A′v` is free of rank 2 over `A′` on both sides, since `A′v = vA′`.
  A left `A`-automorphism `α` of `A^n` restricts to `tr(α) ∈ GL_(2n)(A′)`. The matrix `tr(α)` read in `GL_(2n)(A)` is
  `id ⊗ α` on `A ⊗_(A′) A^n = (A ⊗_(A′) A) ⊗_A A^n`.
- **Step 2 (the bimodule sequence over F_2).** Let `μ: A ⊗_(A′) A → A` be multiplication and `ω = 1⊗v + v⊗1`.
  - `A ⊗_(A′) A` is left free on `1⊗1, 1⊗v`, and `μ(a⊗1 + b⊗v) = a + bv`. In characteristic 2 this gives
    `ker μ = Aω`, with `a ↦ aω` injective.
  - For `c ∈ A′`: `ωc = σ(c)ω` with `σ(c) = vcv^(−1)`. Also `ωv = vω`. Hence `ωb = vbv^(−1)ω` for all `b`.
  - So `ker μ ≅ A_(Ad v) ≅ A` as bimodules, via `x ↦ xv`.
  - `a ↦ 1⊗a` is a right-linear section of `μ`.
  - Tensoring `0 → A → A ⊗_(A′) A → A → 0` with `A^n` over `A` gives an exact sequence of free left modules carrying
    `α, id⊗α, α`. By (K-b), `i_*tr[α] = 2[α]`. Artifact §1, Lemma 1.
- **Step 3 (the reflection inverts the generator).** Take `v = δ_P`, so `v² = 1`,
  `v(fδ_(S^k))v^(−1) = (f∘P)δ_(S^(−k))` and `A = A′ ⊕ A′v`.
  - `binary-subshift-ring-k1-is-half-orbit-index` gives `K_1(A′) = Z[u]` with `u = δ_S`.
  - `vuv^(−1) = u^(−1)`, so by (K-a) `i_*[u] = −i_*[u]`.
- **Step 4 (exponent 4).** For `x ∈ K_1(A)`: `2x = i_*(tr x) ∈ Z·i_*[u]`, which is 2-torsion. So `4x = 0`. Artifact §2.
- **Step 5 (no Morita match).** `K_1(M_m(A)) ≅ K_1(A)` is torsion. `K_1(M_n(LC(X,F_2) ⋊ Z)) ≅ Z` by (K-c) and the
  required claim. Ring isomorphisms induce isomorphisms on `K_1`. Artifact §3. ∎

**Checks.**
- `⟨S,P⟩ ≅ D_∞`. `S` has no periodic points, and `S^kP = id` would force `S² = id`.
- One-point analogue of the mechanism, not covered by the statement. For `A = F_2[D_∞] ⊇ A′ = F_2[t^(±1)]`, Lemma 1
  applies and `K_1(A′) = Z[t]` (Bass–Heller–Swan, as in the model test of `minimal-cantor-crossed-product-k-theory-formula-proof`).
  So again `4·K_1(F_2[D_∞]) = 0`.
- The bimodule identities are verified exactly for `F_2^(Z/n) ⋊ D_n`, `n ∈ {3,4,5,6,8}`, by
  `experiments/dihedral-cantor-k1-exponent-four-2026-09-16/bimodule_check.py`.
