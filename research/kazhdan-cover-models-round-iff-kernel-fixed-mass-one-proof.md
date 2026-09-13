---
rg: 2
id: kazhdan-cover-models-round-iff-kernel-fixed-mass-one-proof
kind: route
title: The Kazhdan cover's bimodule representation has an invariant vector near the corner, and invariant intertwiners land in the kernel's fixed subspace
target: kazhdan-cover-models-round-iff-kernel-fixed-mass-one
requires:
  - fpbs-shalom-property-t-is-open
---

Notation is as in the claim. `||·||_2` is normalized by `d_k`. The Shalom premise is used only in §5.

## 1. Asymptotic representation

For `g, h ∈ Γ` put `m(g,h) = s(g)s(h)s(gh)^(-1) ∈ N`. Then

```text
α_k(g)α_k(h) - α_k(gh) = (ρ_k(m(g,h)) - 1) α_k(gh),
```

whose norm is `||ρ_k(m(g,h)) - 1||_2`, and this tends to 0 by (KC1).

## 2. (c) implies (b), and (b) implies (a)

- **An invariant subspace.** `Fix_N(ρ_k)` is `Γ~`-invariant because `N` is normal. `N` acts
  trivially on it, so `ρ_k` restricted there is a representation `π'_k` of `Γ`.
- **The rounding.** Put `π_k = π'_k ⊕ 1` on `C^(d_k) = E_kC^(d_k) ⊕ (1 - E_k)C^(d_k)`.
  - The unitary `α_k(g) = ρ_k(s(g))` preserves both summands and agrees with `π_k(g)` on the
    first.
  - Hence `||α_k(g) - π_k(g)||_2 <= 2(1 - tr E_k)^(1/2)`, which gives (b).
- **(b) implies (a)** trivially.

## 3. Setting up (a) implies (c)

- **Generators.** Let `S~` be a finite generating set of `Γ~`. Put `F = q(S~)` and
  `M_0 = {x·s(q(x))^(-1) : x ∈ S~}`, a subset of `N`. Every `x ∈ S~` equals `m·s(q(x))` with
  `m ∈ M_0`, so `s(F) ∪ M_0` generates `Γ~`.
- **Bimodule representation.** Let `H_k = M_(d_k × D_k)(C)` with `⟨ξ,η⟩ = Tr(η*ξ)/d_k`, and
  `σ_k(x)ξ = ρ_k(x) ξ π_k(q(x))*`. This is a unitary representation of `Γ~`.
- **Corner vector.** `P_k = [1_(d_k) 0]` has norm 1 and satisfies `P_kP_k* = 1`.
- **Displacement on `s(F)`.** For `g ∈ F`:

  ```text
  ||σ_k(s(g))P_k - P_k||^2  =  ||α_k(g)P_k - P_kπ_k(g)||^2
                            =  ||α_k(g) - P_kπ_k(g)P_k*||^2 + ||P_kπ_k(g)(1 - P_k*P_k)||^2
                            <= ||α_k(g) - P_kπ_k(g)P_k*||^2 + (D_k - d_k)/d_k  ->  0.
  ```

- **Displacement on `M_0`.** For `m ∈ M_0`, `σ_k(m)P_k - P_k = (ρ_k(m) - 1)P_k`, whose norm equals
  `||ρ_k(m) - 1||_2`, and this tends to 0.
- **Propagation.** For a word `x` in `s(F)^(±1) ∪ M_0^(±1)`, `||σ_k(x)P_k - P_k||` is at most the
  sum of the letters' displacements. Fix a Kazhdan pair `(K,κ)` for `Γ~`. Then
  `δ_k = max_(x∈K) ||σ_k(x)P_k - P_k|| -> 0`.

## 4. (a) implies (c)

- **Projection onto invariants.** Let `η_k` be the orthogonal projection of `P_k` onto the
  `σ_k`-invariant vectors.
- **Kazhdan bound.** The orthogonal complement of the invariant vectors is a subrepresentation
  with no nonzero invariant vector, so it has no `(K,κ)`-invariant unit vector. Since `η_k` is
  invariant, `σ_k(x)(P_k - η_k) - (P_k - η_k) = σ_k(x)P_k - P_k`, and therefore

  ```text
  κ ||P_k - η_k||  <=  max_(x∈K) ||σ_k(x)P_k - P_k||  =  δ_k.
  ```

- **Invariant vectors live on `Fix_N`.** An invariant `η` satisfies `ρ_k(x)η = ηπ_k(q(x))` for all
  `x ∈ Γ~`. For `m ∈ N` this reads `ρ_k(m)η = η`, so `E_kη = η`.
- **Conclusion.** Left multiplication by `1 - E_k` is a contraction and `P_kP_k* = 1`, so

  ```text
  1 - tr E_k  =  ||(1 - E_k)P_k||^2  =  ||(1 - E_k)(P_k - η_k)||^2  <=  ||P_k - η_k||^2  <=  δ_k^2/κ^2.
  ```

  This proves (c) and item 3.

## 5. The corollary

- **Covers.** By `fpbs-shalom-property-t-is-open`, every discrete Kazhdan group is a quotient of a
  finitely presented Kazhdan group. Take such `Γ~` with `Γ ≅ Γ~/N`, and define `Γ_L`, `K_L` as in
  the claim. The maps `Γ~ -> Γ_L -> Γ` are surjective, and `K_L` is the image of `N`.
- **Choice of models.**
  - Choose `L_1 < L_2 < ...` from the infinite set of the hypothesis.
  - For each `j`, split a finite-dimensional representation of `Γ_(L_j)` that is nontrivial on
    `K_(L_j)` into irreducibles. One irreducible summand `ρ'_j` is nontrivial on `K_(L_j)`.
  - Put `ρ_j = ρ'_j∘(Γ~ -> Γ_(L_j))`.
- **(KC1) holds exactly.** Every `m ∈ N` equals some `n_l`, so `ρ_j(m) = 1` once `L_j >= l`.
- **Fix_N is zero.** `Fix_N(ρ_j)` is `Γ~`-invariant, so by irreducibility it is `0` or everything.
  It is not everything, because `N` maps onto `K_(L_j)`, which acts nontrivially. So `tr E_j = 0`.
- **No rounding.** By §4, no subsequence of `α_j` rounds flexibly, so `Γ` is not flexibly
  HS-stable.
- **Finite-quotient version.** The left regular representation of a finite quotient of `Γ_L` in
  which some element of `K_L` survives is nontrivial on `K_L`.
- **Profinite version.**
  - Suppose that for all `L >= L_1` every finite-dimensional representation of `Γ_L` is trivial on
    `K_L`.
  - Then every finite quotient of `Γ_(L_1)` factors through `Γ`, so the natural surjection
    `Γ^_(L_1) -> Γ^` of profinite completions is injective, hence an isomorphism.
  - The profinite completion of the finitely presented group `Γ_(L_1)` is presented, as a
    profinite group, by the same generators and relators.
  - So if `Γ^` is not finitely presented as a profinite group, the hypothesis holds for all large
    `L`.

## 6. Relation to Dogon Theorem 1.10

Dogon (arXiv:2211.10492v3, §5) uses the same architecture with `L(Γ_n)` embedded trace-preservingly
in a matrix ultraproduct, which needs hyperlinearity of every `Γ_n`, and concludes that some group
is not hyperlinear. Here the covers' finite-dimensional representations replace the embeddings, and
the Kazhdan projection argument of §4 replaces the ucp lifting step. The price is the profinite
hypothesis on the covers.
