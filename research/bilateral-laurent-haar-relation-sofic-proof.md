---
rg: 2
id: bilateral-laurent-haar-relation-sofic-proof
kind: route
title: Periodic points of the two-sided dual give exact cylinder statistics, exact covariance and vanishing fixed-point proportions, hence a diagonal-plus-permutation embedding of the crossed product
target: bilateral-laurent-haar-relation-is-sofic
requires:
  - paunescu-sofic-action-class-permanence
  - cordeiro-sofic-relation-permanence
---

Notation as in the claim. Everything below also works for `GL_n(A)` in place of `SL_n(A)`.

## Step 0. Imports

* Păunescu (`paunescu-sofic-action-class-permanence`), verbatim:
  * **Definition 1.4.** *"An action α of a countable group G on a standard Borelian space (X,ℬ,μ) is called sofic
    if the crossed product L^∞(X) ⋊_α G embeds in Π_{k→ω} M_{n_k}(ℂ) such that L^∞(X) ⊂ Π_{k→ω} D_{n_k}(ℂ) and
    G ⊂ Π_{k→ω} P_{n_k}(ℂ)."*
  * **Proposition 1.15.** *"Let α be a free action. Then E_α is a sofic equivalence relation if and only if α is a
    sofic action."*
* Cordeiro (`cordeiro-sofic-relation-permanence`): Definition 2.1 of a sofic relation through the measured full
  semigroup `[[R]]` with trace `tr φ = μ{x ∈ dom φ : φ(x) = x}`. The node records that this definition is equivalent
  to Păunescu's.
* Standard fact, used in the same form in `hyperlinear-action-distills-to-stabilizer-coset-bernoulli-proof`, Step 0
  (C2): a trace-preserving `*`-homomorphism of a weakly dense `*`-subalgebra of a tracial von Neumann algebra into a
  tracial von Neumann algebra is isometric in `‖·‖_2`, so it extends to a normal trace-preserving embedding.

## Step 1. The action is a p.m.p. action

* Each `f ∈ A` acts on `Ā` by convolution, `(f y)_k = Σ_e f_e y_(k-e)`. This is a finite sum, so the action is
  continuous. It is a ring action, so `γ ∈ GL_n(A)` acts on `Ā^n` as a continuous automorphism with inverse `γ^(-1)`.
* A continuous automorphism of a compact group preserves Haar measure, and so does translation. The formula
  `(w,γ)(w',γ') = (w + γw', γγ')` matches composition. So `G` acts by measure-preserving homeomorphisms.
* **Finite propagation.** If every entry of `γ` and of `γ^(-1)`, and the vector `w`, are supported in `[-r, r]`, then
  `((w,γ).y)|_F` depends only on `y|_(F + [-r,r])` for every window `F ⊂ Z`. Hence for a cylinder set `C` on `F`, the
  set `g C` is a cylinder set on `F + [-r, r]`.

## Step 2. Essential freeness

Let `g = (w, γ) ≠ e`. Its fixed set is `Fix g = {y : (γ - 1) y = w}`.

* **Case `γ = 1`, `w ≠ 0`.** There are no fixed points.
* **Case `γ ≠ 1`.** `Fix g` is empty or a coset of `K = ker(γ - 1)`, a closed subgroup of `Ā^n`.
  * Pick a nonzero entry `f = (γ - 1)_(ij)`, and let `p_i` be the `i`-th coordinate projection.
  * Then `p_i ∘ (γ - 1)` restricted to the `j`-th coordinate is multiplication by `f` on `Ā`. This map is onto:
    write `f = x^a f_0` with `f_0(0) = 1` and `deg f_0 = s`. The equation `f_0 y = u` is the recursion
    `y_k = u_k + Σ_(e=1..s) (f_0)_e y_(k-e)`. It can be solved in both directions from any initial block, because the
    top coefficient of `f_0` is also 1.
  * So `p_i ∘ (γ - 1)` maps `Ā^n` onto `Ā`, which is uncountable. Its kernel has infinite index, and it contains `K`.
    A closed subgroup of infinite index in a compact group is Haar-null, so `μ(Fix g) = 0`.

## Step 3. Periodic models

* Let `A_m = A/(x^m - 1) = F_2[x]/(x^m - 1)`, where `x` is invertible, and `X_m = A_m^n`, with `N_m = 2^(mn)` points.
  `X_m` is also the set of `m`-periodic points of `Ā^n`.
* Reduction `A -> A_m` is a ring map, so `g = (w,γ) -> ḡ`, `ḡ.y = γ̄ y + w̄`, is an action of `G` on the finite set
  `X_m`. Let `U_g^(m)` be its permutation matrix.
* On periodic points the linear part is literally the restriction: `γ̄ y = γ y` for `y ∈ X_m ⊂ Ā^n`. The translation
  part differs: `w̄` is the periodization `Σ_(t ∈ Z) x^(tm) w`.

**(P1) Exact statistics.** For an interval `I ⊂ Z` of length at most `m`, restriction `X_m -> F_2^(I x n)` is a
surjective group homomorphism. So it pushes the uniform measure to the uniform measure. For a function `f` depending
only on coordinates in `I` (a cylinder function), `N_m^(-1) Σ_(y ∈ X_m) f(y) = ∫ f dμ`.

**(P2) Exact covariance.** Fix a cylinder function `f` on a window `F` and `g = (w,γ)` with propagation `r` and
`supp w ⊂ [-r, r]`. For every `m > diam(F) + 4r + 1` and every `y ∈ X_m`,
`(g.y)|_F = (ḡ.y)|_F`. Indeed, the linear parts agree, and on `F` the periodization `w̄` agrees with `w`, because
no translate `supp w + tm` with `t ≠ 0` meets `F + [-r, r]`. Hence `f(g^(-1) y) = f(ḡ^(-1) y)` on `X_m` for `m` large.
This is applied to `g^(-1)`, whose data also have propagation `r`.

**(P3) Vanishing fixed points.** Let `g ≠ e` and let `Fix_m g` be the fixed set of `ḡ` on `X_m`.
* If `γ = 1` and `w ≠ 0`: once `m` exceeds the span of `w`, the reduction `w̄ ≠ 0`, so `Fix_m g = ∅`.
* If `γ ≠ 1`: `Fix_m g` is empty or a coset of `ker(γ̄ - 1)`. With `f = x^a f_0` as in Step 2 and `m > s`, the map
  `p_i ∘ (γ̄ - 1)` restricted to coordinate `j` is multiplication by `f` on `A_m`. Its kernel is the annihilator of
  `f_0` in `A_m`, of dimension `deg gcd(f_0, x^m - 1) <= s`. So `rank(γ̄ - 1) >= m - s`, and
  `|Fix_m g| / N_m <= 2^(-(m - s)) -> 0`.

The experiment `experiments/bilateral-haar-periodic-2026-09-17/check_periodic_models.py` checks the action property,
the rank bound (280 cases), the translation case and the window covariance (P2) for `n = 3`, with no failures.

## Step 4. The embedding

* Let `𝒞` be the `*`-algebra of cylinder functions. It is weakly dense in `L^∞(Ā^n, μ)`, and `g`-invariant by
  Step 1. Let `M = L^∞(Ā^n) ⋊ G` with trace `τ(f u_g) = δ_(g,e) ∫ f dμ`. Let `M_0 = span{f u_g : f ∈ 𝒞, g ∈ G}`,
  a weakly dense `*`-subalgebra that is the algebraic crossed product `𝒞 ⋊_alg G`.
* Define `θ_m(f u_g) = D_m(f) U_g^(m)`, where `D_m(f)` is the diagonal matrix of `f|_(X_m)`, restricting `f` as a
  function on `Ā^n` to the subset `X_m`. Extend linearly on `𝒞 ⋊_alg G`. Let `θ = (θ_m)_ω` into
  `Π_ω M_(N_m)(C)`.
* **Multiplicativity.** `θ_m(f u_g) θ_m(f' u_h) = D_m(f) D_m(f'∘ḡ^(-1)) U_(gh)^(m)`, while
  `θ_m(f u_g f' u_h) = D_m(f · (f'∘g^(-1))) U_(gh)^(m)`. By (P2) these are equal for all large `m`. Adjoints are the
  same computation, since `(f u_g)^* = (f̄∘g) u_(g^(-1))`. So `θ` is a `*`-homomorphism on `M_0`.
* **Trace.** `tr_(N_m) θ_m(f u_g) = N_m^(-1) Σ_(y ∈ Fix_m g) f(y)`. For `g = e` this equals `∫ f dμ` once `m` exceeds
  the window of `f`, by (P1). For `g ≠ e` it is at most `‖f‖_∞ |Fix_m g| / N_m -> 0`, by (P3). So
  `tr_ω ∘ θ = τ` on `M_0`.
* **Extension.** By the standard fact of Step 0, `θ` extends to a normal trace-preserving embedding of `M`.
* **Diagonal and permutation conditions.** `θ(u_g) = (U_g^(m))_ω` lies in `Π_ω P_(N_m)`. `θ(𝒞) ⊂ Π_ω D_(N_m)`.
  `Π_ω D_(N_m)` is a von Neumann subalgebra, closed in `‖·‖_2` on bounded sets. Every element of the unit ball of
  `L^∞` is a `‖·‖_2`-limit of elements of the unit ball of `𝒞`, and `θ` is `‖·‖_2`-isometric, so
  `θ(L^∞) ⊂ Π_ω D_(N_m)`.

This is Definition 1.4, so the action is sofic (Theorem part 2).

## Step 5. The relation

The action is free by Step 2 (discard the null union of the fixed sets of the countably many `g ≠ e`). Proposition
1.15 then makes `R'` a sofic equivalence relation. This is Păunescu's definition, and it is equivalent to Cordeiro's
Definition 2.1. For a Borel subrelation `S ⊆ R'`, `[[S]] ⊆ [[R']]` with the same trace, so restricting the maps
`π : [[R']] -> [[N]]` of Definition 2.1 to `[[S]]` shows that `S` is sofic (Theorem part 3). ∎

## Remarks

* The same proof works for any subgroup of `A^n x| GL_n(A)`. It uses only finite propagation, and ranks of nonzero
  Laurent matrices over the cyclic quotients.
* The group `GL_fin(W) x| EL_n(A)` of `untwisted-bilateral-symbol-enrichment-is-lef`, with `W = A^n`, acts linearly on
  the dual `Ā^n`. Off the null set of finitely supported points, its orbits coincide with the `G`-orbits. The
  finitary element `1 + e ⊗ v`, with `⟨e, y⟩ = 1` and `⟨e, v⟩ = 0`, moves `y` to `y + v`. So `R'` is also the Haar orbit
  relation of `H_bi`. The mirror fibre product `P ⊂ H_bi` therefore acts inside `R'`.
