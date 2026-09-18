---
rg: 2
id: degree-one-corner-unitaries-fail-the-k-budget-proof
kind: route
title: Apply the graded dichotomy to the corner eRe and carry it to R by Morita invariance through the unital subring eRe x (1-e)R(1-e)
target: degree-one-corner-unitaries-fail-the-k-budget
requires:
  - graded-rings-with-degree-one-units-fail-the-k-budget
  - infinitely-generated-symbols-block-fp-elementary-groups
  - rational-k1-detection-forces-infinite-order-unit-class
  - isometric-frames-over-rank-one-bases-fail-the-k-budget
---

Put `f = 1 - e`. **(M) Morita invariance** (standard, not read at source): for a full idempotent `e`, the corner
inclusion induces isomorphisms `K_n(e R e) -> K_n(R)`, sending the class of a unit `a` of `e R e` to `[a + f]`.

**Item 1.**
- Since `e in R_0`, `e R e = ⊕_k e R_k e` is a grading with unit `e`, and `λ -> λ e` is a unital map `Q -> e R e`.
- `w = e w e`, since `e w = w w' w = w e`, and `w' = e w' e`. So `w` is a unit of `e R e` of degree `1` with inverse `w'`.
- Item 1 of `graded-rings-with-degree-one-units-fail-the-k-budget` gives the skew Laurent structure.
- `u_e (w' + f) = w w' + f = 1`, and similarly `(w' + f) u_e = 1`, since `w f = 0 = f w`. Elements of `Q` are central.

**Item 2.**
- Apply the graded node to `e R e` and `w`. Either `ker(Q^x -> K_1(e R e))` is not finitely generated, or the symbols
  `{λ e, w}_(eRe)` generate a non-finitely generated subgroup of `K_2(e R e)`.
- By (M), `[λ e]` corresponds to `[λ e + f]`, so the first kernel is `Λ_e`.
- **The symbols.** `C = e R e × f R f` is a unital subring of `R`, with unit `e + f = 1`. For `N >= 3`,
  `St_N(C) = St_N(e R e) × St_N(f R f)`. In the Steinberg group of `C`, `{(λ e, f), (w, f)}_C = ({λ e, w}, {f, f}) = ({λ e, w}, 1)`.
  The inclusion `C ⊆ R` sends it to `{λ e + f, u_e}_R`. On the first factor this map is the corner inclusion, so it is
  the (M) isomorphism on `K_2`.
- `λ = (λ e + f)(λ f + e)`, and the three units `λ e + f`, `λ f + e` and `u_e` commute pairwise, since `u_e` lies in
  `e R e + f`. So `{λ, u_e} = {λ e + f, u_e} + {λ f + e, u_e}`, using bimultiplicativity in the commutative subring
  they generate.
- The last symbol is the image of `{(e, λ f), (w, f)}_C = ({e, w}, {λ f, f}) = (1, 1)`, so it vanishes.
- So `{λ, u_e}` corresponds to `{λ e, w}` under (M). In the second case these symbols generate a non-finitely generated
  subgroup of `Sym(R)`. `infinitely-generated-symbols-block-fp-elementary-groups`, item 2, gives the conclusion for
  every `N >= 3`.

**Item 3.**
- For `λ in Q^x`, idempotent matrices `g` give `[λ g + (1 - g)] in K_1(R)`. This is additive on orthogonal sums and
  invariant under equivalence of idempotents, so it defines a homomorphism `μ_λ : K_0(R) -> K_1(R)`. `μ_λ[1] = [λ]` and
  `μ_λ[e] = [λ e + f]`.
- `t[1] = n[e]` gives `t[λ] = n[λ e + f]`. For `λ in Λ_e` this is `0`, so `λ^t in ker(Q^x -> K_1(R))`.
- `Q^x / {±1}` is free abelian, so `λ -> λ^t` is injective modulo `±1`. So `{λ^t : λ in Λ_e}` is not finitely
  generated, and neither is the kernel.

**Item 4.** A rational relation `[1] = c[e]` with `c != 0` gives integers `t >= 1`, `n != 0` and a torsion element
`z` with `t[1] - n[e] = z`. Replacing `(t, n)` by `(o t, o n)`, where `o` is the order of `z`, gives an exact relation.
Then items 2 and 3 apply.

**Item 5.**
- `x = x y x = φ(e) x` and `p φ(e) = t s t e s = t e s = φ(e)`, so `p x = x`.
- `w' w = y t s x = y p x = y x = e`, and `w w' = s x y t = s φ(e) t = (s t) e (s t) = e`.
- The degrees are right: `s_i in R_1`, `t_i in R_(-1)`, and `x`, `y` have entries in `B ⊆ R_0`.

**Item 6.** For an idempotent matrix `g` over `B`, `(t g)(g s) = t g s = φ(g)` and `(g s)(t g) = g (s t) g = g`. So `g` and
`φ(g)` are equivalent over `R`, and `[φ(g)] = [g]` in `K_0(R)`. This is item 1 of the matricial frame node, applied
to `g`.

**Item 7.**
- (a) `t[1_B] in (1 - A) K_0(B)` for some `t >= 1` gives `t[1_R] = 0` by item 6. Then use
  `rational-k1-detection-forces-infinite-order-unit-class`.
- (b) Each factor of `B` has `K_0 = Q` with idempotents of every class in `[0,1] ∩ Q`. So for small rational `ε > 0`
  there is an idempotent `e in B` with `[e] = ε v`. `[φ(e)] = A[e] = [e]`, so cancellation in matricial rings (as in
  the matricial frame node) gives `φ(e) ~ e` in `M_k(B)`. From `[1_B] = c v + (1 - A) z`, clearing denominators gives
  `t[1_B] - n[e] in (1 - A) K_0(B)`, with `n = t c / ε`. Here `c != 0`, since otherwise (a) holds. `e != 0` is full,
  because `R` is simple. Then items 5, 6 and 4 apply.
- (c) If `dim coker(1 - A) = 1` and `v ∉ (1 - A) Q^m`, then `Q^m = Q v + (1 - A) Q^m`. For an irreducible nonnegative
  matrix with spectral radius `1`, the eigenvalue `1` is simple, with a positive eigenvector `v`. Since
  `dim ker = dim coker = 1` and `1` is not a repeated root, `v` is not in the image. That is Perron--Frobenius,
  standard.
