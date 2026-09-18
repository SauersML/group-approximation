---
rg: 2
id: leavitt-tensor-powers-k-vanishing-via-farrell-jones-proof
kind: route
title: Assemble K of the crossed product C ∗ Z^(d−1) from K-trivial skew Laurent rings over the regular coefficient ring
target: leavitt-tensor-powers-have-vanishing-k-theory-in-all-degrees
requires:
  - leavitt-tensor-powers-are-twisted-crossed-products
  - leavitt-crossed-product-coefficient-ring-is-k-trivial
  - virtually-poly-z-groups-satisfy-fjc-with-additive-coefficients
  - crossed-product-rings-inherit-fjc-with-additive-coefficients
  - regular-coherent-laurent-coefficients-kill-twisted-nil-terms
  - ara-cortinas-leavitt-tensor-k-theory-vanishes
artifacts:
  - research/artifacts/leavitt-tensor-k-theory-farrell-jones-2026-09-12.md
---

Let `k` be a field, `L = L_k(1,2)`, and `K` non-connective algebraic `K`-theory.

**Step 0: `d = 1`.** `K_n(L) = 0` for every `n` is Ara–Cortiñas Proposition 6.2
with `R = k` (`ara-cortinas-leavitt-tensor-k-theory-vanishes`). From now on
`d >= 2`.

**Step 1: the crossed product in Bartels–Reich form.** Take `Λ ≅ Z^(d−1)`,
`C = L_0^(⊗(d−1)) ⊗ L` and the units `u^λ` of
`leavitt-tensor-powers-are-twisted-crossed-products`, with `u^0 = 1`. Then
`L^(⊗d) = ⊕_λ u^λ C`, and `u^λ C = C u^λ`. Put

```text
α_λ(c) = u^λ c (u^λ)^(−1),    τ_(λ,μ) = u^λ u^μ (u^(λ+μ))^(−1) ∈ C^x.
```

- `(c u^λ)(c' u^μ) = c α_λ(c') τ_(λ,μ) u^(λ+μ)`, and `α_0 = id`.
- So `L^(⊗d) ≅ C_(α,τ)Λ` in the sense of Bartels–Reich. The identities (τ-τ) and
  (α-α) hold by associativity.
- For `H <= Λ` the restricted crossed product is the subring
  `C_(α|,τ|)H = ⊕_(h ∈ H) C u^h`.

**Step 2: Farrell–Jones.** By `crossed-product-rings-inherit-fjc-with-additive-coefficients`
there is an additive `Λ`-category `A = A_(α,τ)` with:
- `H_n^Λ(Λ/H; K_A) ≅ K_n(C_(α|,τ|)H)` for every `H` and `n`;
- `H_n^Λ(pt; K_A) ≅ K_n(L^(⊗d))`.

`Λ ≅ Z^(d−1)` is poly-`Z`. So by
`virtually-poly-z-groups-satisfy-fjc-with-additive-coefficients`,
`H_n^Λ(E_VCyc Λ; K_A) -> K_n(L^(⊗d))` is bijective for every `n ∈ Z`.

**Step 3: every orbit value vanishes.** `Λ` is torsion-free abelian, so its
virtually cyclic subgroups are `1` and the infinite cyclic groups `Zλ`.
1. **`H = 1`.** `C_(α|,τ|)1 = C`, and `K_n(C) = 0` for every `n` (part 3 of
   `leavitt-crossed-product-coefficient-ring-is-k-trivial`).
2. **`H = Zλ` with `λ ≠ 0`.**
   - **The ring.** `u^(mλ) (u^λ)^(−m)` is a unit of `Λ`-degree `0`, so it lies
     in `C^x`. Hence `C_(α|,τ|)H = ⊕_(m ∈ Z) C t^m` with `t = u^λ`, and
     `(c t^m)(c' t^n) = c φ^m(c') t^(m+n)` for `φ = α_λ`. This is the skew Laurent
     ring `C_φ[t, t^−1]`.
   - **Its coefficients are regular.** `C[Z^m] = C[t_1^±, ..., t_m^±]` is
     regular coherent for every `m >= 0`.
     - `R = C[t_1, ..., t_m]` is regular coherent (part 2 of the coefficient-ring
       claim). It is coherent, and every finitely presented module has finite
       projective dimension, so it has a finite resolution by finitely generated
       projectives.
     - `C[Z^m] = S^(−1) R` for the central multiplicative set `S` of monomials.
       A finitely presented `S^(−1)R`-module has a presentation matrix whose
       denominators can be cleared by the central units `t^a`, so it is
       `S^(−1)N` for a finitely presented `R`-module `N`. Since `S^(−1)R` is flat
       over `R`, localizing a finite projective resolution of `N` resolves it.
     - The side of the modules does not matter. `x_i ↦ y_i` defines an
       anti-automorphism of `L` that preserves `L_0`. Tensored up and fixing each
       `t_i`, it gives an anti-automorphism of `C[Z^m]`, which exchanges left and
       right modules and preserves finite presentation and projectivity.
   - **The Nil terms vanish.** By
     `regular-coherent-laurent-coefficients-kill-twisted-nil-terms`,
     `K(C_φ[t, t^−1])` is the mapping torus of `K(φ^−1)` on `K(C) ≃ 0`, and so is
     contractible.

   Hence `H_n^Λ(Λ/H; K_A) = 0` for every `H ∈ VCyc` and every `n ∈ Z`.

**Step 4: the source vanishes.**
- `E_VCyc Λ` is a `Λ`-CW-complex whose cells have the form `Λ/H × D^k` with
  `H ∈ VCyc`.
- `H_*^Λ(−; K_A)` is a `Λ`-homology theory defined by an `Or(Λ)`-spectrum
  (Davis–Lück), so it satisfies the disjoint union axiom and commutes with the
  colimit over skeleta.
- **Induction on skeleta.** The relative groups of `(X_k, X_(k−1))` are sums of
  groups `H_(n−k)^Λ(Λ/H; K_A) = 0`. So `H_n^Λ(X_k; K_A) = 0` for all `k` and
  `n`, and `H_n^Λ(E_VCyc Λ; K_A) = 0` for all `n`.
- These two properties of `Or`-spectrum homology theories are standard. They
  were not re-read from Davis–Lück here.

**Step 5.** Bijectivity in Step 2 gives `K_n(L^(⊗d)) = 0` for every `n ∈ Z`. ∎

## Referee (bh-ref-misc, 2026-09-18): PASS, including Step 3.2

Internal referee lane, not an external review. The application that matters is `d = 4` over `F_p`,
which gives `K_1 = K_2 = 0` for `L_p^(⊗4)`.

**Step 3.2 (regular coherence of `C[Z^m]`).** The step is correct and complete.
- **The definition.** It is the one in the Bartels–Lück hypothesis, as quoted in
  `regular-coherent-laurent-coefficients-kill-twisted-nil-terms`: every finitely presented module
  is of type FP. So coherence does not need a separate check. If every finitely presented module is
  FP, then a finitely generated submodule of a finitely presented `M` is the kernel of a map between
  FP modules, and so is FP.
- **The argument.**
  - The monomials are central non-zero-divisors of `R = C[t_1, …, t_m]`, so `R ⊆ S^(−1)R`.
  - A presentation matrix over `S^(−1)R` becomes a matrix over `R` after multiplying its rows by
    central units, which leaves the cokernel unchanged. So `M ≅ S^(−1)R ⊗_R N` with `N` finitely
    presented, by right exactness.
  - Base change along the flat map `R → S^(−1)R` carries a finite resolution of `N` by finitely
    generated projectives to one of `M`.
  - The involution `x_i ↔ y_i` preserves `L_0`, so left and right modules behave the same.
- **The open problem Bartels–Lück record is not used here.** That problem asks whether regular
  coherence passes from `R` to `R[t]` in general. Here the polynomial case is proved directly (part 2
  of `leavitt-crossed-product-coefficient-ring-is-k-trivial`: `C[t_1, …, t_p]` is a colimit of
  `M_N(L[t_1, …, t_p])` along free extensions, and `L` is regular supercoherent by Ara–Cortiñas
  Lemma 6.1). The Laurent case then needs only central localization.

**The rest of the chain**, checked:
- `L^(⊗d)` is strongly `Z^d`-graded, and `v = λ + (Σ v_i) e_d` with `λ ∈ Λ` is unique. So
  `L^(⊗d) = ⊕_λ u^λ C`, and the `u_j` and their inverses check.
- The `Zλ`-subrings are skew Laurent rings: `u^(mλ)(u^λ)^(−m)` has `Λ`-degree `0`.
- `K_*(C) = colim K_*(L) = 0`, by Ara–Cortiñas Proposition 6.2 with `R = k`.
- The Farrell–Jones inputs are theorems for `Z^(d−1)` with additive coefficients and for crossed
  products (Bartels–Reich).

**Trust surface.**
- The literature: Ara–Cortiñas; Bartels–Lück Theorem `the:The_non_connective_K-theory_of_additive_categories`;
  Lück–Steimle; Farrell–Jones for `Z^n`; Bartels–Reich.
- Step 4's two standard properties of `Or`-spectrum homology theories (recalled, not read).
- No step is special to `d = 2`, so `d = 4` is covered.
