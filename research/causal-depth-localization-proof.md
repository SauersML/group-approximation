---
rg: 2
id: causal-depth-localization-proof
kind: route
title: The causal rule is an operator identity inside one ball; induction on depth, using only that depth indicators lie in the commutative base algebra, puts every finite-depth computation projection into that algebra from both sides
target: causal-depth-localizes-quantum-noncommutativity
requires:
  - fp-v-times-subshift-full-groups-force-quantum-rigidity
---

Notation as in the target. Fix a `D`-quantum family `E_(a,c)(z)` on `W_0`, with `D >= R`, and assume
(B). For a pattern `p` on `W`, write `[p](z) = ∏_(w ∈ W) B_(p(w))(zw)`.

## Step 0. Ball sums

Take sites inside one ball `z B_D`. Products of family members, or of marginals, at such sites commute
by (Q2), since the ball has diameter `2D`. A product prescribing a partial pattern on such sites that
no point of `X` realizes vanishes. To see this, expand over the extensions to `z B_D` by (Q1), and
apply (Q3) to each term. This is Step 0 of `quantum-rigidity-product-stability-proof`.

## Step 1. The base algebra

By (B), the `B_a(z)` generate a commutative algebra `𝒜`. They satisfy (Q1). They also satisfy (Q3)
for `Y_D`: a `B_D`-pattern absent from `π_A(X)` has vanishing marginal product, by Step 0.

The compactness step of `quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products-proof` then gives
a unital homomorphism `ι : LC(Y_D, k) → 𝒜`. It sends each cylinder to the product of the prescribed
marginals. Its image is `𝒜`, since it contains every generator.

## Step 2. The causal rule as an operator identity

For every `z`, every pattern `p` on `W`, and every `c`:

```text
[p](z) C_c(z) = C_c(z) [p](z) = Σ_(g ∈ C^(P(p)), Θ_p(g) = c)  [p](z) ∏_(u ∈ P(p)) C_(g(u))(zu),     (∗)
```

and all factors on the right commute.

*Proof.* The sites `zW ∪ {z}` lie in `z B_R ⊆ z B_D`, so all the operators involved commute
(Step 0).
- Insert `Σ_g ∏_u C_(g(u))(zu) = I`.
- Terms with `Θ_p(g) ≠ c` prescribe a pattern that no point of `X` realizes, by the causal rule, so
  they vanish.
- For `Θ_p(g) = c`, the product `[p](z) ∏_u C_(g(u))(zu)` absorbs `C_c(z)`, because the terms with
  `C_(c')(z)`, `c' ≠ c`, vanish for the same reason. ∎

## Step 3. Item 1, by induction on `n`

Put `a_(n,c)(z) = ι{ω : depth_ω(z) <= n, val_ω(z) = c}`. The claim is
`e_n(z) C_c(z) = C_c(z) e_n(z) = a_(n,c)(z)`.

**Base, `n = 0`.** `e_0(z) = Σ_(p : P(p) = ∅) [p](z)`. For such `p`, (∗) reads
`[p](z) C_c(z) = C_c(z)[p](z) = [Θ_p() = c] [p](z)`. Summing over `p` gives `a_(0,c)(z)`.

**Step `n - 1 → n`.**
- *Depth recursion.* `depth(z) <= n` iff every predecessor of `z` has depth `<= n - 1`. In `𝒜` this
  reads `e_n(z) = Σ_p [p](z) ∏_(u ∈ P(p)) e_(n-1)(zu)`, and all factors are in `𝒜`.
- *Left multiplication.* Using (∗),

  ```text
  e_n(z) C_c(z) = Σ_p Σ_(Θ_p(g) = c) ( ∏_u e_(n-1)(zu) ) ( ∏_u C_(g(u))(zu) ) [p](z).
  ```

  Here `[p](z)` was moved to the right, past the `C(zu)` of its own ball, and it commutes with the
  `e`'s in `𝒜`.
- *The interleaving lemma.* Let `u_1, …, u_m` list `P(p)`, and write `ε_i = e_(n-1)(z u_i)`,
  `γ_i = C_(g(u_i))(z u_i)` and `α_i = a_(n-1, g(u_i))(z u_i)`. By induction `ε_i γ_i = α_i ∈ 𝒜`.
  The `ε_i` and `α_i` all lie in the commutative algebra `𝒜`. Hence

  ```text
  ε_1 ⋯ ε_m γ_1 ⋯ γ_m = (ε_2 ⋯ ε_m)(ε_1 γ_1) γ_2 ⋯ γ_m = α_1 (ε_2 ⋯ ε_m) γ_2 ⋯ γ_m = … = α_1 ⋯ α_m .
  ```

  Only the commutation of the `ε`'s with each other and with the `α`'s is used. No `ε_i` is ever
  moved past a `γ_j` with `j ≠ i`.
- *So* `e_n(z) C_c(z) = Σ_p Σ_(Θ_p(g) = c) α_1 ⋯ α_m [p](z) ∈ 𝒜`. Read through `ι`, this is the
  classical recursion `val_ω(z) = Θ_p((val_ω(zu))_u)` on `{depth <= n}`. So the sum equals
  `a_(n,c)(z)`.
- *Right multiplication.* Write (∗) with `[p](z)` on the left, and put the `e`'s on the right. The
  mirror lemma `γ_1 ⋯ γ_m ε_1 ⋯ ε_m = α_1 ⋯ α_m` holds in the same way: absorb `ε_m` into `γ_m`
  first, then move `α_m` right, past the remaining `ε`'s. So `C_c(z) e_n(z) = a_(n,c)(z)` as well. ∎

## Step 4. Item 2

Let `E = E_(a,c)(z) = B_a(z) C_c(z)` and `E' = E_(a',c')(z')`, and write `e = e_n(z)`,
`e' = e_n(z')`.
- By item 1, `eE = Ee = B_a(z) a_(n,c)(z) =: β ∈ 𝒜`, and likewise `e'E' = E'e' = β' ∈ 𝒜`.
- Hence `e e' E E' = e' (eE) E' = e' β E' = β e' E' = β β'`.
- In the same way `e e' E' E = β' β`, and `E E' e e' = β β'`, `E' E e e' = β' β`.
- Since `𝒜` is commutative, `e e' [E, E'] = [E, E'] e e' = 0`. ∎

## Step 5. Item 3

- `{depth(1) <= n}` is an increasing sequence of clopen subsets of `Y_D` whose union, by assumption,
  is all of `Y_D`. By compactness, one of them, say `n = N`, is all of `Y_D`.
- The causal rule is translation invariant, so `depth_ω(z) = depth_(z^(-1)ω)(1) <= N` for all `z`.
- Hence `e_N(z) = ι(Y_D) = I`, and item 1 gives `C_c(z) = a_(N,c)(z) ∈ 𝒜`.
- Every `E_(a,c)(z) = B_a(z) C_c(z)` then lies in `𝒜`, so the family commutes. ∎

## Step 6. Item 4

`𝒜` is a finite-dimensional commutative algebra spanned by idempotents. So `𝒜 = ⊕_π kπ` over its
minimal idempotents `π`, which sum to `I`.
- *Points.* `f ↦ (coefficient of π in ι(f))` is a unital homomorphism `LC(Y_D, k) → k` taking
  `{0,1}` values on indicators. It is therefore evaluation at a unique point `ω_π ∈ Y_D`, the
  intersection of the clopen sets it sends to `1`.
- *Good idempotents.* Call `π` good if `depth_(ω_π)(z) < ∞` for every `z`, and put
  `p = Σ_(π good) π`.
- *`p` commutes with the family.* Fix a good `π` and a site `z`, and let `N = depth_(ω_π)(z)`. Then
  `π e_N(z) = π`. By item 1, `π C_c(z) = π e_N(z) C_c(z) = π a_(N,c)(z)`, and similarly
  `C_c(z) π = a_(N,c)(z) π`. These agree, so `π` commutes with every `C_c(z)`, and so does `p`.
  `p` commutes with the base marginals because it lies in `𝒜`.
- *The splitting.* Put `W_fin = p W_0` and `W_∞ = (I - p) W_0`. Both are invariant.
  - On `W_fin`, every `C_c(z)` acts as `Σ_(π good) a_(N_π(z), c)(z) π ∈ 𝒜`, so the family commutes
    there.
  - The base spectrum of `W_∞` is `{ω_π : π not good}`. ∎
