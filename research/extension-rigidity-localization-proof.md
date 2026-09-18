---
rg: 2
id: extension-rigidity-localization-proof
kind: route
title: Central base marginals make the space a module over locally constant functions on the base; localize at each point, where the base is a classical scalar field, and recover commutators by compactness
target: extension-rigidity-is-base-centrality-plus-pointwise-rigidity
requires:
  - fp-v-times-subshift-full-groups-force-quantum-rigidity
---

Notation as in the target. Write `[β]` for the cylinder of a pattern `β` on a finite set, and
`1_U` for the indicator of a clopen `U ⊆ B^Λ`.

## Step 1. Reduction to fibre marginals

Let `E` be base-central. Summing over `(b', f)` shows that every `E^B_b(v)` commutes with every
`E^B_(b')(u)` and every `E^F_f(u)`. At one site, orthogonality gives
`E^B_b(u) E^F_f(u) = Σ_(f') E_(b,f')(u) · Σ_(b') E_(b',f)(u) = E_(b,f)(u)`. So `E` commutes if and
only if the fibre marginals commute pairwise.

Every product of operators at sites of one ball `pB_D` is a product of pairwise commuting
idempotents (Q2), so its order does not matter.

## Step 2. The module structure

`LC(B^Λ, k)` is the directed union over finite `S ⊂ Λ` of `LC(B^S, k) = ⊗_(u ∈ S) k^B`. The
partitions of unity `(E^B_b(u))_b` commute pairwise, so there is a unital homomorphism

```text
ψ : LC(B^Λ, k) → End_k(W_0),    ψ(1_[β]) = ∏_(u ∈ S) E^B_(β(u))(u)   for β ∈ B^S.
```

Its image `R` is commutative, and every fibre marginal commutes with `R`.

## Step 3. Localization

For `z ∈ B^Λ` put `N_z = ⋃ { ψ(1_U) W_0 : U clopen, z ∉ U }`.
- This union is directed, since `ψ(1_U) = ψ(1_(U ∪ U')) ψ(1_U)`. So `N_z` is a subspace.
- It is invariant under `R` and under every fibre marginal, since these commute with each
  `ψ(1_U)`.

Put `M_z = W_0 / N_z`. Every operator commuting with `R` induces an operator on `M_z`, and this
is an algebra homomorphism from the commutant of `R` to `End(M_z)`.

- **Scalars.** `E^B_b(u)` acts on `M_z` as `[z(u) = b]`.
  - If `z(u) = b`, then `I − E^B_b(u) = ψ(1_U)` with `U = {x : x(u) ≠ b}`, and `z ∉ U`.
  - If `z(u) ≠ b`, then `E^B_b(u) = ψ(1_[b@u])` with `z ∉ [b@u]`.
  - In both cases the difference from the scalar maps `W_0` into `N_z`.
- **Lemma (compactness).** If `w ∈ N_z` for every `z ∈ B^Λ`, then `w = 0`.
  - *Choosing neighbourhoods.* For each `z` there is a clopen `U_z ∌ z` with `w ∈ ψ(1_(U_z)) W_0`,
    so `ψ(1_(U_z)) w = w`. With `V_z = B^Λ \ U_z ∋ z`, this says `ψ(1_(V_z)) w = 0`.
  - *Compactness.* Finitely many `V_z` cover the compact space `B^Λ`. Refine them to a clopen
    partition `P_1, …, P_m` with each `P_j ⊆ V_(z_j)`.
  - *Conclusion.* `ψ(1_(P_j)) w = ψ(1_(P_j)) ψ(1_(V_(z_j))) w = 0`, so
    `w = Σ_j ψ(1_(P_j)) w = 0`. `∎`

## Step 4. Points off `Y` localize to zero

Let `z ∉ Y`. Every forbidden pattern of `Y` lies in a ball of radius `≤ D`, so some ball pattern
`β = z|_(pB_D)` does not occur in `Y`. Then no point of `X` has base letters `β` on `pB_D`.
Expanding each `E^B_(β(w))(w) = Σ_f E_(β(w),f)(w)` over the ball gives
`ψ(1_[β]) = Σ_(φ ∈ F^(pB_D)) ∏_(w) E_(β(w),φ(w))(w)`. Every term vanishes by (Q3) for `X`.
So `I = ψ(1_(B^Λ \ [β]))`, with `z ∉ B^Λ \ [β]`, and `N_z = W_0`. That is, `M_z = 0`.

## Step 5. The localized fibre family is `y`-relative

Let `y ∈ Y` and write `Ḡ_f(u)` for the operator induced by `E^F_f(u)` on `M_y`.
- (Q1) and (Q2) pass to images under an algebra homomorphism.
- (Q3_y): let `φ ∈ F^(pB_D)` be such that no point of `X` carries `(y|_(pB_D), φ)` on `pB_D`.
  Inserting the base partition of unity on the ball and using Step 1,

  ```text
  ∏_(w ∈ pB_D) E^F_(φ(w))(w) = Σ_(β ∈ B^(pB_D)) ψ(1_[β]) ∏_(w) E^F_(φ(w))(w)
                             = Σ_β ∏_(w) E_(β(w),φ(w))(w).
  ```

  - The term `β = y|_(pB_D)` is `0` by (Q3) for `X`.
  - For `β ≠ y|_(pB_D)`, we have `y ∉ [β]`, so the term maps `W_0` into `N_y` and vanishes on
    `M_y`.

  Hence `∏_w Ḡ_(φ(w))(w) = 0`.

## Step 6. Item 1

Take fibre marginals `A = E^F_f(u)` and `A' = E^F_(f')(u')`. The commutator `[A, A']` commutes
with `R`, and it induces `[Ḡ_f(u), Ḡ_(f')(u')]` on each `M_y`.
- If `[A, A'] = 0`, every localization commutes.
- Conversely, suppose every localization at `y ∈ Y` commutes. Then for each `w ∈ W_0`, the vector
  `[A, A'] w` lies in `N_y` for `y ∈ Y`, and in `N_z = W_0` for `z ∉ Y` by Step 4. By the Lemma,
  `[A, A'] w = 0`.

Step 1 turns this into commutation of `E`. The scalar statement is Step 3.

## Step 7. Item 2

Let `G` be a `y`-relative `D`-family on `W` and put `E_(b,f)(u) = [y(u) = b] G_f(u)`.
- (Q1): `Σ_(b,f) E_(b,f)(u) = Σ_f G_f(u) = I`. Orthogonality holds because the `G_f(u)` are
  orthogonal and the scalars are `0/1`.
- (Q2) is inherited from `G`.
- (Q3): let `(β, φ)` on `pB_D` not occur in `X`. The product `∏ E` is
  `[β = y|_(pB_D)] ∏_w G_(φ(w))(w)`. This is `0` when `β ≠ y|_(pB_D)`, and by (Q3_y) otherwise.
- Base marginals are the scalars `[y(u) = b]`, so `E` is base-central, and `E^F_f(u) = G_f(u)`.
  By Step 1, `E` commutes if and only if `G` does.

## Step 8. Item 3

- **(⇒)** If `X` is `D`-rigid, every family commutes and so is base-central, which is (C_D).
  Let `G` be a `y`-relative family with `y ∈ Y`. Its lift from Step 7 commutes, and hence so
  does `G`.
- **(⇐)** Let `E` be any `D`-family. By (C_D) it is base-central. By Steps 5–6 it commutes as soon
  as each localization at `y ∈ Y` commutes, and each localization is a `y`-relative `D`-family.
  So relative rigidity at every `y` finishes the proof. `∎`

**Remark (what the proof uses).** Only (Q1)–(Q3) and the compactness of `B^Λ` are used. Nothing
depends on the dimension of `W_0` or on the characteristic. This is why the finite-dimensional
minimal-idempotent argument of the transplant node extends to all `W_0`. The minimal
idempotents there are replaced by the stalks `M_y`.
