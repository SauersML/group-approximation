---
rg: 2
id: bernoulli-infinite-power-iff-approximate-half-absorption-proof
kind: route
title: Capture a dense sequence of sets by splitting the remainder after each set is chosen, and read off half-splittings from the coordinates of the power
target: bernoulli-infinite-power-iff-approximate-half-absorption
requires:
  - bernoulli-shifts-with-equal-base-entropy-are-isomorphic
  - bernoulli-isomorphism-collapse-set-is-a-subgroup
---

Notation as in the target. All σ-algebras are taken mod null sets, and isomorphisms of factor actions are
isomorphisms of measure algebras commuting with `Γ`. Standard realization turns such isomorphisms of the full
measure algebra into point isomorphisms of actions.

**Independent generating families.** If `A_1, …, A_n, C` are independent `Γ`-invariant sub-σ-algebras
generating `B_X`, with isomorphisms `(X, A_i) ≅ X_i` and `(X, C) ≅ Y`, then the joint map is a measure-preserving
equivariant isomorphism `X ≅ X_1 × … × X_n × Y`: independence gives the product measure, generation gives
injectivity. The same holds for countable families `(A_n)_(n≥1)`.

**(2) ⇒ (1).** Fix a dense sequence `(B_j)` in the measure algebra of `X`. Enumerate `j(1), j(2), …` so that every
`j` occurs infinitely often. We build independent `Γ`-invariant `A_1, …, A_n, C_n` generating `B_X`, with every
`(X, A_i)` and `(X, C_n)` isomorphic to `X`. Start with `C_0 = B_X`.

- **Stage `n+1`.** Put `B = B_(j(n+1))` and `η = 2^(-n-2)`. Finite unions of rectangles `S ∩ T`, with
  `S ∈ A_1 ∨ … ∨ A_n` and `T ∈ C_n`, are dense in `B_X`. So there are finite partitions `P ⊆ A_1 ∨ … ∨ A_n` and
  `R ⊆ C_n` and a union `U` of atoms of `P ∨ R` with `μ(B Δ U) < η`.
- **Split the remainder.** Transport item 2 through `(X, C_n) ≅ X`, with `R` and `δ = η/|R|`. This gives
  independent `Γ`-invariant `A_(n+1), C_(n+1) ⊆ C_n` generating `C_n`, both isomorphic to `X`, with every atom `r`
  of `R` within `δ` of some `r' ∈ A_(n+1)`.
- **Capture.** Replace each `p ∩ r` in `U` by `p ∩ r'`, giving `U' ∈ A_1 ∨ … ∨ A_(n+1)`. The atoms of `P` are
  disjoint, so `U Δ U' ⊆ ∪_r (r Δ r')` and `μ(U Δ U') ≤ |R| δ = η`. Hence `B` is within `2^(-n-1)` of
  `A_1 ∨ … ∨ A_(n+1)`.
- The family `A_1, …, A_(n+1), C_(n+1)` is independent and generates `B_X`, since `A_(n+1) ∨ C_(n+1) = C_n`.

**Limit.** Put `A_∞ = ∨_n A_n`. Each `B_j` is within `2^(-n-1)` of `A_∞` for infinitely many `n`, and `A_∞` is
closed in the measure algebra, so `B_j ∈ A_∞`. Density gives `A_∞ = B_X`. The `A_n` are independent, since every
finite subfamily is, and each is isomorphic to `X`. By the paragraph on generating families, `X ≅ X^N`.

**(1) ⇒ (2).** Let `Ψ: X → X^N` be an isomorphism, and `R`, `ε` given. Cylinder sets on finitely many
coordinates are dense, so there is `n` with `Ψ(R) ⊂_ε σ(coordinates 0, …, n−1)`. Let `A` be the preimage of the
σ-algebra of the coordinates `{0, …, n−1} ∪ {n, n+2, n+4, …}` and `C` that of `{n+1, n+3, …}`. They are
independent, invariant and generating. Each index set is infinite, so `(X, A) ≅ X^N ≅ X ≅ (X, C)`. And
`R ⊂_ε A`.

**(2) ⇔ (3).** Fix a half-splitting `(A, C)`.
- Given a half-splitting `(A', C')` with `R ⊂_ε A'`, choose isomorphisms `φ: (X, A') → (X, A)` and
  `ψ: (X, C') → (X, C)`, both through `X`. By the paragraph on generating families, `φ ∨ ψ` is an automorphism `T`
  of `X` with `T(A') = A`, so `T(R) ⊂_ε A`.
- Conversely, if `T(R) ⊂_ε A`, then `(T^(-1) A, T^(-1) C)` is a half-splitting with `R ⊂_ε T^(-1) A`.

Item 2 with `R` trivial gives a half-splitting, so `X ≅ X × X`.

**Corollary.** `X_h^N` is the Bernoulli shift with base `(L^N, λ^N)`, where `(L, λ)` is the base of `X_h`, and
`H(λ^N) = ∞` because `H(λ) > 0`. Seward's Theorem 1.1 (first prerequisite) applies to standard bases of infinite
entropy, so `X_h^N ≅ X_∞`. Item 2 for `X_h` is therefore `X_h ≅ X_∞`. Item 5 of the second prerequisite gives
`X_(h') ≅ X_∞` for `h' ≥ h`, `D(G) = R` and `h^Rok_sup(G) = 0`.
