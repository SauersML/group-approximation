# The loop braid cloning systems are properly graded, and V_loop is finitely generated

Lane z2-12-loop-bv, 2026-09-13. Unreviewed hand proof. Source definitions are from
Witzel–Zaremsky, *Thompson groups for systems of groups, and their finiteness properties*,
arXiv:1405.5491v3 (Groups Geom. Dyn. 12 (2018)), read from the v3 PDF: Definition 2.16 (p. 18),
Definition 2.18 (p. 19), equation (2.5) (p. 18), Proposition 5.9 and Lemma 5.10 (pp. 31–32), and
Section 10 (pp. 53–55).

## 0. Setup and conventions

- `F_n` is free on `x_1, …, x_n`, and `F_n ⊂ F_{n+1}` in the obvious way.
- `LB_n = ΣAut_n`: automorphisms sending each `x_i` to a conjugate of some `x_j` (no inverses).
  `PLB_n = PΣAut_n` is the pure part.
- WZ generators (p. 53): `β_i: x_i ↦ x_{i+1}, x_{i+1} ↦ x_{i+1}^{-1} x_i x_{i+1}` and
  `σ_i: x_i ↔ x_{i+1}`, fixing all other generators.
- **Product convention.** WZ write maps on the right, and their relation list (from FRR97) holds for
  the right action `x^{gh} = (x^g)^h`. Test on `x_{i+2}` with `i = 1`:
  - `β_1β_2σ_1` sends `x_3 → x_3^{-1}x_2x_3 → x_3^{-1}x_1x_3`;
  - `σ_2β_1β_2` sends `x_3 → x_2 → x_2^{-1}x_1x_2 → x_3^{-1}x_1x_3`.
  They agree. Under the composition reading the two sides give `x_3^{-1}x_2^{-1}x_1x_2x_3` and
  `x_2^{-1}x_3^{-1}x_1x_3x_2`, which differ.
- **Left form.** For `g ∈ LB_n`, let `L(g) ∈ Aut(F_n)` be `x ↦ x^{g^{-1}}`.
  - Then `L(gh) = L(g) ∘ L(h)`, and `L` is an isomorphism of `LB_n` onto `ΣAut_n` with
    composition.
  - Write `x_i^{g} = w x_{π_g(i)} w^{-1}`. Then `π_{gh} = π_h ∘ π_g`, so `g ↦ π_g^{-1}` is a
    homomorphism to `S_n` that sends `β_i, σ_i` to `(i i+1)`.
  - It therefore equals WZ's `ρ_n`, and `L(g)(x_i)` is a conjugate of `x_{ρ_n(g)(i)}`.
- Directed system: `ι_{n,n+1}(g)` acts as `g` on `x_1, …, x_n` and fixes `x_{n+1}`. So
  `L(ι(g)) = ι(L(g))`, and `im ι_{n,n+1}` consists of the elements whose left form fixes `x_{n+1}`
  and preserves `F_n`.
- Cloning maps, WZ (10.1)–(10.2), with `ε = ±1`:
  - `(β_i^ε)κ_k` is `β_{i+1}^ε` for `k < i`, `β_i^ε β_{i+1}^ε` for `k = i`,
    `β_{i+1}^ε β_i^ε` for `k = i+1`, and `β_i^ε` for `k > i+1`;
  - `σ_i` is cloned the same way.
  - WZ Lemma 10.1: these give cloning systems on `LB_*` and on `PLB_*`, so (FCS1)
    `(gh)κ_k = (g)κ_{ρ(h)k} (h)κ_k` holds for all g, h, together with (2.5).
- **Merge maps.** `δ_k: F_n → F_{n+1}` sends `x_i ↦ x_i (i < k)`, `x_k ↦ x_k x_{k+1}`,
  `x_i ↦ x_{i+1} (i > k)`.
  - `δ_k` maps the basis of `F_n` onto a subset of the basis
    `B_k = {x_1, …, x_{k−1}, y_k = x_k x_{k+1}, x_{k+1}, x_{k+2}, …, x_{n+1}}` of `F_{n+1}`.
  - So `δ_k` is injective, and its image is the free factor spanned by `B_k \ {x_{k+1}}`.

## 1. Lemma A (cloning commutes with merging)

**Lemma A.** For all `g ∈ LB_n` and `1 ≤ k ≤ n`: `L((g)κ_k) ∘ δ_k = δ_{ρ(g)(k)} ∘ L(g)`.

*Generators.* Put `a_i := L(β_i)`, so `a_i: x_i ↦ x_i x_{i+1} x_i^{-1}, x_{i+1} ↦ x_i`, and
`s_i := L(σ_i)`, which swaps `x_i, x_{i+1}`. Check the relation on each generator of `F_n`; the
unlisted generators are shifted or fixed identically on both sides.

- `β_i`, `k = i`, `ρ(β_i)(i) = i+1`. The left side is `(a_i ∘ a_{i+1}) ∘ δ_i`.
  - `x_i ↦ x_i x_{i+1}`, then `a_{i+1}` gives `x_i x_{i+1} x_{i+2} x_{i+1}^{-1}`, then `a_i` gives
    `x_i x_{i+1} x_{i+2} x_i^{-1}`. The right side gives
    `δ_{i+1}(x_i x_{i+1} x_i^{-1}) = x_i x_{i+1} x_{i+2} x_i^{-1}`.
  - `x_{i+1} ↦ x_{i+2} ↦ x_{i+1} ↦ x_i`. The right side gives `δ_{i+1}(x_i) = x_i`.
- `β_i`, `k = i+1`, `ρ(β_i)(i+1) = i`. The left side is `(a_{i+1} ∘ a_i) ∘ δ_{i+1}`.
  - `x_i ↦ x_i ↦ x_i x_{i+1} x_i^{-1} ↦ x_i x_{i+1} x_{i+2} x_{i+1}^{-1} x_i^{-1}`. The right side
    gives `δ_i(x_i x_{i+1} x_i^{-1})`, which is the same word.
  - `x_{i+1} ↦ x_{i+1} x_{i+2} ↦ x_i x_{i+2} ↦ x_i x_{i+1}`. The right side gives
    `δ_i(x_i) = x_i x_{i+1}`.
- `β_i`, `k < i`: `a_{i+1} ∘ δ_k = δ_k ∘ a_i`, since `δ_k` shifts `x_i, x_{i+1}` to
  `x_{i+1}, x_{i+2}` and fixes `x_k x_{k+1}`, which `a_{i+1}` also fixes.
- `β_i`, `k > i+1`: `a_i ∘ δ_k = δ_k ∘ a_i`, since `δ_k` fixes `x_i, x_{i+1}`.
- `σ_i`, `k = i`: `(s_i ∘ s_{i+1})(x_i x_{i+1}) = x_{i+1} x_{i+2} = δ_{i+1}(x_{i+1})`, and
  `(s_i ∘ s_{i+1})(x_{i+2}) = x_i = δ_{i+1}(x_i)`.
- `σ_i`, `k = i+1`: `(s_{i+1} ∘ s_i)(x_i) = x_{i+2} = δ_i(x_{i+1})`, and
  `(s_{i+1} ∘ s_i)(x_{i+1} x_{i+2}) = x_i x_{i+1} = δ_i(x_i)`.
- `σ_i`, `k < i` and `k > i+1`: as for `β_i`.

*All elements.* (FCS1) with `g = h = 1` gives `(1)κ_k = 1`. For `ε = −1`, (FCS1) applied to
`β_i β_i^{-1} = 1` forces `(β_i^{-1})κ_k = ((β_i)κ_{ρ(β_i)k})^{-1}`, which agrees with (10.1).
Taking inverses of the relation for `β_i` at index `ρ(β_i)k` gives it for `β_i^{-1}` at index k.

If the relation holds for g at every index and for h at every index, then
`L((gh)κ_k) ∘ δ_k = L((g)κ_{ρ(h)k}) ∘ L((h)κ_k) ∘ δ_k = L((g)κ_{ρ(h)k}) ∘ δ_{ρ(h)k} ∘ L(h)
= δ_{ρ(g)ρ(h)k} ∘ L(g) ∘ L(h) = δ_{ρ(gh)k} ∘ L(gh)`.

Induction on word length finishes the proof. ∎

## 2. Free-group facts used

- (F1) The centralizer of `x_p` in a free group is `⟨x_p⟩`.
  - Free factors are malnormal: if `w A w^{-1} ∩ A ≠ 1` then `w ∈ A`.
  - If `F = A ∗ B` and an automorphism φ of F satisfies `φ(A) ⊆ A` and `φ(B) = B`, then
    `φ(A) = A`. Proof: the retraction `r: F → A` killing B satisfies `r ∘ φ = φ|_A ∘ r`, and `r ∘ φ`
    is onto.
- (F2) If two free factors are spanned by subsets of one common basis, their intersection is spanned
  by the intersection of the subsets, by reduced words.
- (F3) Let `y = x_n x_{n+1}`, `D = ⟨x_1, …, x_{n−1}, y⟩ = δ_n(F_n)` and
  `A = ⟨x_1, …, x_n⟩ ⊂ F_{n+1}`.
  - Write an element of D as a reduced word in the basis `{x_1, …, x_{n−1}, y}`. The letter form
    over `x_1, …, x_{n+1}` has no cancellation: blocks `x_n x_{n+1}` and `x_{n+1}^{-1} x_n^{-1}`
    never cancel against each other or against `x_i^{±1}` with `i ≤ n−1`.
  - Hence such an element lies in A only if it has no `y^{±1}` letter, so `D ∩ A = F_{n−1}`.
  - Let `u' ∈ D` be reduced with last letter `x_i^{±1}` (`i ≤ n−1`), and set
    `E = u' y u'^{-1} x_{n+1}^{-1}`. The segment `x_i^{±1} x_n x_{n+1} x_i^{∓1}` of E is
    reduced. The final `x_{n+1}^{-1}` can cancel at most one letter of `u'^{-1}`, so the middle
    `x_{n+1}` survives and `E ∉ A`.

## 3. Theorem (proper grading)

**Theorem.** The cloning systems on `LB_*` and `PLB_*` are properly graded (WZ Definition 2.16).

*Proof.* Suppose `(h)κ^n_k = ι_{n,n+1}(ḡ)` with `h, ḡ ∈ LB_n` and `1 ≤ k ≤ n`. Put
`φ = L(h) ∈ Aut(F_n)` and `ψ = L((h)κ_k) = ι(L(ḡ))`. So `ψ(x_{n+1}) = x_{n+1}` and
`ψ(A) = A` for `A = F_n ⊂ F_{n+1}`. Let `j = ρ(h)(k)`. Lemma A gives `ψ ∘ δ_k = δ_j ∘ φ`.

**Case k < n.**
- *Step 1.* Write `φ(x_n) = w x_p w^{-1}` with `p = ρ(h)(n) ≠ j`. Then
  `x_{n+1} = ψ(δ_k(x_n)) = δ_j(w) x_{p'} δ_j(w)^{-1}`, where `δ_j(x_p) = x_{p'}` is a single
  generator (as `p ≠ j`).
- *Step 2.* Abelianizing gives `p' = n+1`, so `p = n` and `j < n`. Then
  `δ_j(w) ∈ ⟨x_{n+1}⟩ = δ_j(⟨x_n⟩)` by (F1), so `w ∈ ⟨x_n⟩` and `φ(x_n) = x_n`.
- *Step 3.* For `i < n`, `δ_k(x_i)` is a word in `x_1, …, x_n` (as `k+1 ≤ n`). So
  `δ_j(φ(x_i)) = ψ(δ_k(x_i)) ∈ A ∩ δ_j(F_n)`.
- *Step 4.* By (F2) applied to the basis `B_j`, this intersection is `δ_j(F_{n−1})`, because
  `A = span{x_1, …, x_{j−1}, y_j, x_{j+1}, …, x_n}` and
  `δ_j(F_n) = span(B_j \ {x_{j+1}})`. So `φ(x_i) ∈ F_{n−1}`.

**Case k = n.**
- *Step 1.* `ψ(x_n) x_{n+1} = ψ(δ_n(x_n)) = δ_j(φ(x_n)) = u x_j x_{j+1} u^{-1}` with
  `u = δ_j(w)`, where `φ(x_n) = w x_j w^{-1}`.
- *Step 2.* `ψ(x_n)` is a conjugate of a single generator. Abelianizing gives `j = n`.
- *Step 3.* Then `u ∈ D`, and `E := u y u^{-1} x_{n+1}^{-1} = ψ(x_n) ∈ A`. Write `u = u' y^b` with
  `u'` reduced over `{x_1, …, x_{n−1}, y}` and not ending in `y^{±1}`. By (F3), `u' = 1`.
- *Step 4.* So `u = y^b = δ_n(x_n^b)`, hence `w = x_n^b` and `φ(x_n) = x_n`.
- *Step 5.* For `i < n`, `ψ(x_i) = ψ(δ_n(x_i)) = δ_n(φ(x_i)) ∈ D ∩ A = F_{n−1}` by (F3). So
  `φ(x_i) ∈ F_{n−1}`.

**Both cases.**
- φ fixes `x_n` and maps `F_{n−1}` into itself, so by (F1) it restricts to an automorphism
  `φ̄` of `F_{n−1}`.
- `φ̄` is symmetric: if `w x_p w^{-1} ∈ F_{n−1}` then `p ≤ n−1`, and `w` may be taken in
  `F_{n−1}` by malnormality.
- So `h = ι_{n−1,n}(h̄)` with `h̄ := L^{-1}(φ̄) ∈ LB_{n−1}`, which is pure when h is.
- By (2.5), `ι(ḡ) = (ι(h̄))κ^n_k` equals `ι_{n,n+1}((h̄)κ^{n−1}_k)` for `k ≤ n−1`, and equals
  `ι_{n−1,n+1}(h̄)` for `k = n`. The convention there is `κ^{n−1}_n := ι_{n−1,n}`.
- Injectivity of `ι` gives `ḡ = (h̄)κ^{n−1}_k`, which is Definition 2.16. ∎

## 4. Corollary (finite generation)

WZ Lemma 5.10 (p. 32), verbatim: "Let G∗ be a family of groups equipped with a properly graded
cloning system, with cloning maps κ^n_k. Suppose that for n sufficiently large, all G_n are
finitely generated and also are generated by the images of the cloning maps with codomain G_n.
Then T(G∗) is finitely generated."

For `n ≥ 5`, `LB_n` is generated by the `β_i, σ_i`, `1 ≤ i ≤ n−1` (WZ p. 53: "The β_i together
with the σ_i generate ΣAut_n"). Every such generator is a cloning image:
- if `i ≤ n−3`, then `β_i = (β_i)κ^{n−1}_{n−1}`, by the case `k > i+1` of (10.1) with
  `β_i ∈ LB_{n−1}`;
- if `i ∈ {n−2, n−1}`, then `i ≥ 3`, and `β_i = (β_{i−1})κ^{n−1}_1`, by the case `k < i−1`;
- the same holds for `σ_i` by (10.2).

With the Theorem, **`V_loop = T(LB_*)` is finitely generated.**

## 5. Scope

- Not claimed:
  - finite presentability or higher finiteness of `V_loop` or `F_loop`;
  - finite generation of `F_loop` (the pure generators `α_{ij}` with `i ≤ 2 < n−1 ≤ j` are not
    visibly cloning images, so that case is left open);
  - type F∞ of `LB_n` (a citation still to verify).
- Proposition 5.9 upgrades the Theorem to type F_n as soon as `L_k(LB_*)` is eventually
  (n−1)-connected and `LB_n` is of type F_n.
