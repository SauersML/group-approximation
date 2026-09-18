---
rg: 2
id: lifted-thompson-t-relative-t-forces-dyadic-twist-gap-proof
kind: route
title: Tensor products, ultraproducts and the word length of z give the structure of c; the finite eigenspace splitting of r_k and induction from C_T(r_k) identify dyadic twists with Thompson T; a weighted sum of matrix-coefficient cnd functions gives (c)
target: lifted-thompson-t-relative-t-forces-dyadic-twist-gap
requires:
  - lifted-thompson-t-quotients-are-rotation-centralizers
---

**Imported standard facts.**
- (CND) For a unitary representation `π` and a vector `ξ`, the function
  `g ↦ ‖π(g)ξ − ξ‖²` is cnd. It is the cnd function of the affine action `v ↦ π(g)v + π(g)ξ − ξ`.
  Nonnegative combinations and pointwise limits of cnd functions are cnd. (Bekka–de la Harpe–Valette,
  *Kazhdan's property (T)*, §C.2.)
- (Ind) For `H ≤ G` and a unitary representation `σ` of `H` on `K`, the induced representation
  `ρ = Ind_H^G σ` contains `K` as the sections supported on the coset `H`. That subspace is
  `ρ(H)`-invariant, and `ρ|_H` acts on it as `σ`.
- (U) Ultraproducts. Fix a nonprincipal ultrafilter `U` on `N` and unitary representations `π_n`
  on `H_n`. Bounded sequences modulo `U`-null ones form a Hilbert space `H_U`, and
  `π_U(g)[(η_n)] = [(π_n(g)η_n)]` is a unitary representation. Its norms are
  `‖[(η_n)]‖ = lim_U ‖η_n‖`.

**Sum of squares (used twice).** Let `H = ⊕_j E_j` be an orthogonal decomposition into
`π(S)`-invariant subspaces, and `ξ` a unit vector with `max_s ‖π(s)ξ − ξ‖ ≤ m`. Write
`ξ = Σ ξ_j`. Then

`Σ_j Σ_s ‖π(s)ξ_j − ξ_j‖² = Σ_s ‖π(s)ξ − ξ‖² ≤ |S| m² = |S| m² Σ_j ‖ξ_j‖²`.

So some `j` with `ξ_j ≠ 0` has `max_s ‖π(s)ξ_j − ξ_j‖ ≤ √|S| m ‖ξ_j‖`.

## (a) Structure of `c`

- *`c(0) = 0`:* use the trivial representation.
- *Symmetry:* the conjugate representation `π̄` has `π̄(z) = e(−θ)` and the same norms.
- *Subadditivity:* take `π` and `π'` with twists `θ` and `θ'`. Then `π ⊗ π'` has
  `z ↦ e(θ + θ')`. With `ζ = ξ ⊗ ξ'`,

  `‖(π⊗π')(s)ζ − ζ‖ ≤ ‖(π(s)ξ − ξ) ⊗ π'(s)ξ'‖ + ‖ξ ⊗ (π'(s)ξ' − ξ')‖ = ‖π(s)ξ − ξ‖ + ‖π'(s)ξ' − ξ'‖`.

  Take the max over `s`, then the infimum.
- *Lower semicontinuity:* let `θ_n → θ` with `c(θ_n) → a`, and pick `π_n`, `ξ_n` with
  `max_s ‖π_n(s)ξ_n − ξ_n‖ ≤ c(θ_n) + 1/n`. In `π_U`:
  - `π_U(z)[(η_n)] = [(e(θ_n)η_n)] = e(θ)[(η_n)]`, because `|e(θ_n) − e(θ)| · ‖η_n‖ → 0` for
    bounded sequences. So `π_U(z) = e(θ)·I`.
  - `ξ = [(ξ_n)]` is a unit vector with `‖π_U(s)ξ − ξ‖ = lim_U ‖π_n(s)ξ_n − ξ_n‖ ≤ a`.

  Hence `c(θ) ≤ a`.
- *Lower bound:* write `z = s_1 ⋯ s_L`. The triangle inequality gives
  `|e(θ) − 1| = ‖π(z)ξ − ξ‖ ≤ L max_s ‖π(s)ξ − ξ‖`, so `c(θ) ≥ |e(θ) − 1| / L`.
- *Consequences:* `c > 0` off `0`. A lower semicontinuous function attains its infimum on a
  compact set, so `c` has a positive minimum on each closed arc avoiding `0`.

## (b) Dyadic twists are Thompson's T

**First inequality, `inf_k ε_k ≤ c(j/2^k)` whenever `2^k ∤ j`.**
- Let `π` have `π(z) = e(j/2^k)`. Then `π(z^{2^k}) = 1`, so `π` factors through
  `T̄/⟨z^{2^k}⟩`.
- By `lifted-thompson-t-quotients-are-rotation-centralizers`, `σ(ι_k(g)) := π(g)` is then a
  well-defined unitary representation of `C_T(r_k)` on `K`.
- Let `ρ = Ind_{C_T(r_k)}^T σ`, and view `ξ ∈ K ⊂ H_ρ` by (Ind).
- Then `ρ(r_k)ξ = σ(ι_k(z))ξ = e(j/2^k)ξ`. The eigenvalue is `≠ 1`, so `ξ ⊥ ker(ρ(r_k) − 1)`.
- Also `ρ(ι_k(s))ξ = π(s)ξ`, so `ε_k ≤ max_s ‖π(s)ξ − ξ‖`.

**Second inequality, `inf_{dyadic} c ≤ √|S| ε_k`.**
- Let `ρ`, `k` and `ξ ⊥ ker(ρ(r_k) − 1)` have `max_s ‖ρ(ι_k(s))ξ − ξ‖ ≤ m`.
- `r_k` has order `2^k` in `T`, so `(ker(ρ(r_k) − 1))^⊥ = ⊕_{j=1}^{2^k−1} E_j`, where `E_j` is
  the `e(j/2^k)`-eigenspace of `ρ(r_k)`.
- `r_k` is central in `C_T(r_k) = ι_k(T̄)`, so each `E_j` is invariant under `π := ρ ∘ ι_k`, and
  `π(z)|_{E_j} = ρ(r_k)|_{E_j} = e(j/2^k)`.
- Sum of squares gives some `j ∈ [1, 2^k − 1]` with `c(j/2^k) ≤ √|S| m`.

**The "iff".** Since `c` has a positive minimum away from `0` by (a), `inf_{dyadic ≠ 0} c > 0` is
equivalent to `liminf c` along nonzero dyadics tending to `0` being positive.

## (c) An unbounded cnd function from small nonzero twists

- Suppose `inf_{θ≠0} c = 0`. Choose `θ_n ≠ 0`, `π_n` and unit `ξ_n` with `π_n(z) = e(θ_n)` and
  `max_s ‖π_n(s)ξ_n − ξ_n‖ ≤ 2^{-n}`.
- Put `ψ(g) = Σ_n 2^n ‖π_n(g)ξ_n − ξ_n‖²`.
- *Convergence:* if `g` has `S`-length `ℓ`, the `n`-th term is at most
  `2^n (ℓ 2^{-n})² = ℓ² 2^{-n}`. So `ψ` is finite, and it is cnd by (CND).
- *Unboundedness:* `ψ(z^M) ≥ 2^n |e(Mθ_n) − 1|²`. For `θ_n ∉ Z`, some multiple `Mθ_n` lies in
  `[1/3, 2/3] mod 1`:
  - if `θ_n` is irrational, the multiples are dense;
  - if `θ_n = a/q` in lowest terms with `q ≥ 2`, the multiples are all of `(1/q)Z/Z`.

  So `sup_M ψ(z^M) ≥ 3 · 2^n` for every `n`.
- *Conclusion:* `ψ` is cnd and unbounded on `⟨z⟩`, which is the negation of
  `lifted-thompson-t-center-has-relative-t`.
- *Hence Gap_T:* if that node holds, `inf_{θ≠0} c > 0`, so in particular the dyadic infimum is
  positive, which is `Gap_T` by (b). ∎
