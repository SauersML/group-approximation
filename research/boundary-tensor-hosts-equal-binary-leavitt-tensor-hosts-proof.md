---
rg: 2
id: boundary-tensor-hosts-equal-binary-leavitt-tensor-hosts-proof
kind: route
title: Transfer group-algebra embeddings between B ⊗ L_∂(d) and B ⊗ L(1,2) through Brownlowe–Sørensen one way and a binary Leavitt corner the other way
target: boundary-tensor-hosts-equal-binary-leavitt-tensor-hosts
requires:
  - boundary-crossed-product-is-a-leavitt-path-algebra
  - countable-graph-leavitt-path-algebras-embed-in-binary-leavitt
  - boundary-crossed-product-carries-leavitt-family
  - leavitt-algebras-l-k-1-n-are-simple
---

Notation: `R = L_∂(d) = LC(∂F_d, F) ⋊ F_d`, `L = L_F(1,2)`, and all tensor products are over the field `F`.

We use two standard facts.
- **(T)** If `α : A -> A'` is injective, then `id_B ⊗ α : B ⊗ A -> B ⊗ A'` is injective, since over a field
  tensoring is exact.
- **(X) Augmentation extension.** Let `S` be a unital ring, `E ∈ S` an idempotent, and `φ : A -> ESE` a
  homomorphism with `φ(1) = E`, where `A` is an augmented unital algebra with augmentation `ε`. Put
  `ψ(a) = φ(a) + ε(a)(1 − E)`.
  - `φ(a)(1 − E) = 0 = (1 − E)φ(a)`, so `ψ(a)ψ(b) = φ(ab) + ε(ab)(1 − E) = ψ(ab)`.
  - `ψ(1) = E + 1 − E = 1`.
  - `E ψ(a) E = φ(a)`, so `ψ` is injective when `φ` is.

For `F[G]`, `ε(g) = 1` for every `g`.

**(1 ⇒ 2).**
1. `boundary-crossed-product-is-a-leavitt-path-algebra` gives a unital isomorphism `R ≅ L_F(E_d)`, where `E_d`
   is a finite graph with `2d` vertices.
2. `countable-graph-leavitt-path-algebras-embed-in-binary-leavitt` (Brownlowe–Sørensen, Theorem 4.1, with coefficient
   ring `F`; `E^0` is finite) gives a unital injective `ι : L_F(E_d) -> L`.
3. By (T), `id_B ⊗ ι : B ⊗ R -> B ⊗ L` is unital and injective. Composing it with the given embedding proves 2.

**(2 ⇒ 1).**

*Step 1: a nonzero idempotent `e` of `R`.* Take the unital Leavitt family `s_i, t_i` (`i = 1..d`) of
`boundary-crossed-product-carries-leavitt-family`, with `t_i s_j = δ_ij` and `Σ_i s_i t_i = 1`. Put
`e = Σ_(i=1)^(d−1) s_i t_i`.
- It is idempotent, since `(s_i t_i)(s_j t_j) = δ_ij s_i t_i`.
- It is nonzero, since `t_1 e s_1 = 1` (here `d >= 2`, so the index `1` occurs in the sum).

*Step 2: `eR ≅ R^(d−1)` as right `R`-modules.* The map `(r_1, ..., r_(d−1)) ↦ Σ s_i r_i` goes from `R^(d−1)` to
`eR`. Its inverse is `x ↦ (t_1 x, ..., t_(d−1) x)`:
- `t_j Σ s_i r_i = r_j`;
- `Σ s_i t_i x = e x = x` for `x ∈ eR`.

In the same way, the full family gives `R ≅ R^d`.

*Step 3: `eR ⊕ eR ≅ eR`.* We have `eR ⊕ eR ≅ R^(2d−2) = R^d ⊕ R^(d−2) ≅ R ⊕ R^(d−2) = R^(d−1) ≅ eR`. When `d = 2`,
read `R^0 = 0`.

*Step 4: a binary Leavitt family in `eRe`.* Let `Φ : eR ⊕ eR -> eR` be a right-module isomorphism with inverse `Ψ`.
Put `x_1 = Φ(e,0)`, `x_2 = Φ(0,e)` and `(y_1, y_2) = Ψ(e)`.
- `x_1 = Φ((e,0)e) = x_1 e`, and `x_1 ∈ eR`, so `x_1 ∈ eRe`. The same argument gives `x_2, y_1, y_2 ∈ eRe`.
- `Ψ(x_j) = Ψ(e x_j) = Ψ(e) x_j = (y_1 x_j, y_2 x_j)`. Since `ΨΦ = id`, this equals `(e,0)` for `j = 1` and `(0,e)`
  for `j = 2`. So `y_i x_j = δ_ij e`.
- `e = ΦΨ(e) = Φ((e,0) y_1 + (0,e) y_2) = x_1 y_1 + x_2 y_2`.

So `X_i ↦ x_i`, `Y_i ↦ y_i` defines a homomorphism `λ : L -> eRe` with `λ(1) = e`, and `λ ≠ 0` because `e ≠ 0`. It
is injective by `leavitt-algebras-l-k-1-n-are-simple`.

*Step 5: the corner embedding.* By (T), `id_B ⊗ λ : B ⊗ L -> B ⊗ eRe = E(B ⊗ R)E` is injective, with
`E = 1 ⊗ e`, and it sends `1` to `E`. Let `θ : F[G] -> B ⊗ L` be the given unital embedding. Then
`φ = (id_B ⊗ λ) θ : F[G] -> E(B ⊗ R)E` is injective with `φ(1) = E`.

*Step 6: unitalize.* By (X), `ψ(a) = φ(a) + ε(a)(1 − E)` is a unital injective homomorphism `F[G] -> B ⊗ R`. This
proves 1.

**Corollaries.**
- (C1) is the case `F = F_2`, `B = B_Ω`.
- (C2): if a corner `eRe` has commuting units `u, v` with no Laurent relation, then `φ : F_2[Z^2] -> eRe`,
  `(m,n) ↦ u^m v^n`, is injective with `φ(1) = e`. By (X) it becomes a unital embedding into `R`. Conversely take
  `e = 1`. Finally, apply the claim with `B = F_2`.
