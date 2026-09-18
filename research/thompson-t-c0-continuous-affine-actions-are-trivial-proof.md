---
rg: 2
id: thompson-t-c0-continuous-affine-actions-are-trivial-proof
kind: route
title: "T is C^0-dense in Homeo+(S^1); continuous unitary representations extend to the closure, die on point stabilizers (Megrelishvili), and point stabilizers generate; perfectness kills the translation part"
target: thompson-t-c0-continuous-affine-actions-are-trivial
requires: []
---

Notation as in the target. `G = Homeo+(S^1)` and `G̃ = Homeo~(S^1)`, both with the sup metric
(on `S^1 = R/Z` and on `R` respectively). `p : G̃ → G` is the covering homomorphism, with kernel
`⟨z⟩`. `Γ` is `T` or `T̄`, and `Ḡ` is `G` or `G̃` accordingly.

**Imports.**
- (M) Megrelishvili, *Every semitopological semigroup compactification of the group H+[0,1] is
  trivial*, Semigroup Forum 63 (2001) 357–370.
  - It is restated verbatim in Glasner–Megrelishvili, *Banach representations and affine
    compactifications of dynamical systems*, arXiv:1204.0432, Remark 1.25(2): "There exists a
    nontrivial Polish group G whose universal semitopological compactification GWAP is trivial.
    This is shown in [47] for the Polish group G := H+[0, 1] of orientation preserving
    homeomorphisms of the unit interval. Equivalently: every (weakly) continuous representation
    G → Iso(V) of G on a reflexive Banach space V is trivial." Here [47] is the Semigroup Forum
    paper.
  - The Polish topology of `H+[0,1]` is the compact-open topology, which is the sup-metric topology.
    Hilbert spaces are reflexive. So every strongly continuous unitary representation of
    `H+[0,1]` is trivial.
- (F) Cannon–Floyd–Parry, *Introductory notes on Richard Thompson's groups*, Lemma 4.2 (standard;
  wording not re-checked). For dyadic `0 = x_0 < … < x_n = 1` and `0 = y_0 < … < y_n = 1` there is
  `f ∈ F` with `f(x_i) = y_i`.
- (P) `T` is simple, hence perfect (CFP), and `T̄` is perfect: Step 2 of
  `lifted-thompson-t-perfect-centre-cubically-elliptic-proof`, a self-contained argument from `T`
  perfect and dyadic PL interpolation.
- (U) Standard facts about Polish groups.
  - A continuous homomorphism between topological groups is uniformly continuous for the two-sided
    uniformities.
  - A Polish group is complete in its two-sided uniformity.
  - `U(H)` with the strong topology is Polish for separable `H`.
  - Hence a continuous homomorphism from a dense subgroup of a Polish group into `U(H)` extends
    uniquely to a continuous homomorphism of the whole group.
- (GNS) Bekka–de la Harpe–Valette, *Kazhdan's property (T)*, Prop. 2.10.2 (Schoenberg / GNS for
  cnd kernels). For cnd `ψ` on a group `Γ` with `ψ(e) = 0` there is an affine isometric action
  `(π, b)` on a real Hilbert space with `ψ(g) = ‖b(g)‖²`, and one may take `b(Γ)` to be total.

## Step 1. `Γ` is dense in `Ḡ`

**`T` in `G`.** Let `h ∈ G` and `ε > 0`.
- By uniform continuity, choose `m` with `2^{-m} < ε` such that `h` moves each arc
  `[i/2^m, (i+1)/2^m]` onto an arc of length `< ε`. Put `x_i = i/2^m` for `0 ≤ i ≤ 2^m`.
- The points `h(x_i)` for `i < 2^m` are distinct and in cyclic order. Choose dyadic `y_i` with
  `d(y_i, h(x_i)) < ε`, in the same cyclic order.
- Let `R ∈ T` be the rotation by `−y_0`, which is dyadic. Then `0 = R(y_0) < R(y_1) < … < 1`,
  as real numbers in `[0,1)`. Put the endpoint value `R(y_{2^m}) := 1`.
- By (F) there is `f ∈ F ≤ T` with `f(x_i) = R(y_i)`. Put `g = R^{-1} f ∈ T`.
- For `x ∈ [x_i, x_{i+1}]`, `g(x)` lies in the arc `[y_i, y_{i+1}]` and `h(x)` lies in
  `[h(x_i), h(x_{i+1})]`. Both arcs lie within `2ε` of `h(x_i)`. So `d(g(x), h(x)) < 4ε` for all
  `x`.

**`T̄` in `G̃`.** `p` is a continuous open homomorphism with discrete kernel. Indeed `G̃ → G` is a
covering: two lifts of the same map differ by an integer translation, hence have sup-distance
`≥ 1` from each other.
- Let `U ⊂ G̃` be open and non-empty. Then `p(U)` is open, so it meets `T`, at `t` say.
- Choose `u ∈ U` with `p(u) = t`. Then `u ∈ p^{-1}(T) = T̄`.

## Step 2. Continuous unitary representations of `Ḡ` are trivial

Let `ρ` be a strongly continuous unitary representation of `Ḡ`.
- **Stabilizers.** For `a ∈ S^1`, the stabilizer `G_a` is topologically isomorphic to
  `H+[0,1]`: cut the circle at `a`, and the sup metrics agree.
  - For `ã ∈ R`, the stabilizer `G̃_ã` consists of periodic lifts fixing `ã + Z`. Restriction to
    `[ã, ã+1]` is a topological isomorphism onto `H+[0,1]`, because by periodicity the sup over
    `R` equals the sup over one period.
  - By (M), `ρ` is trivial on every point stabilizer.
- **Generation in `G`.** Let `g ∈ G`, fix `a`, and put `q = g(a)`. If `q = a` then `g ∈ G_a`. Otherwise choose `r ∉ {a, q}`.
  Then `S^1 ∖ {r}` is an open arc containing `a` and `q`. So there is `k ∈ G_r` with `k(q) = a`.
  Hence `kg ∈ G_a` and `g = k^{-1}(kg)`.
- **Generation in `G̃`.** Let `g̃ ∈ G̃`, fix `ã`, and put `q̃ = g̃(ã)`.
  - Choose `q̃ = t_0, t_1, …, t_N = ã` with `|t_j − t_{j+1}| < 1/2`.
  - For each `j` pick `r̃_j` with `t_j, t_{j+1} ∈ (r̃_j, r̃_j + 1)`. Let `k_j` be a homeomorphism
    of `[r̃_j, r̃_j + 1]` fixing the endpoints with `k_j(t_j) = t_{j+1}`, extended periodically.
    Then `k_j ∈ G̃_{r̃_j}`.
  - `k_{N−1} ⋯ k_0 g̃` fixes `ã`. So `g̃` is a product of point-fixing elements. (In particular
    `z` is such a product.)
- Hence `ρ = 1`.

## Step 3. Items (A) and (B)

**(A).** Let `π` be a `C^0`-strongly continuous unitary representation of `Γ`, and let `v` be a
vector. `Γ` is countable, so the cyclic subspace `H_v = span(π(Γ)v)` is separable and invariant.
- `π|H_v : Γ → U(H_v)` is continuous. By Step 1 and (U) it extends to a continuous
  representation of `Ḡ`.
- By Step 2 that extension is trivial. So `π(g)v = v` for every `g`.
- `v` was arbitrary, so `π = 1`.

**(B).** Let `α(g)v = π(g)v + b(g)` be `C^0`-continuous. Then `π(g)v = α(g)v − α(g)0` is
continuous in `g` for each `v`, so `π = 1` by (A).
- Then `b(gh) = b(g) + b(h)` is a homomorphism `Γ → (H, +)`.
- It vanishes by (P). So `α` is trivial.

## Step 4. Item (C)

Let `ψ` be cnd with `ψ(e) = 0`, continuous at `e` for `C^0`. Take `(π, b)` from (GNS), with
`b(Γ)` total.
- The cocycle identity gives `b(x) − b(y) = π(y) b(y^{-1}x)`, so `‖b(x) − b(y)‖² = ψ(y^{-1}x)`.
- Fix `h ∈ Γ`. Then `π(g)b(h) − b(h) = (b(gh) − b(h)) − b(g)`, so
  `‖π(g)b(h) − b(h)‖ ≤ ψ(h^{-1}gh)^{1/2} + ψ(g)^{1/2}`.
- Conjugation by `h` is a homeomorphism of `Ḡ`. So the right side tends to `0` as `g → e` in `C^0`.
- `π` is unitary and `b(Γ)` is total, so `π` is strongly continuous. The closed span of `b(Γ)`
  is separable because `Γ` is countable.
- By (A), `π = 1`. Then `b` is a homomorphism to `(H, +)`, so `b = 0` by (P). Hence `ψ = 0`.

## Step 5. Item (D)

Let `(X, μ)` be standard σ-finite and nonsingular for `T`, with `κ` `C^0`-continuous.
- By (A) for `Γ = T`, `κ(q) = 1` for all `q ∈ T`.
- Choose a countable separating family of Borel sets `A_n` of finite measure: intersect a
  countable separating Borel family with a finite-measure exhaustion `X_j`, and add the `X_j`. Then
  `κ(q)1_{A_n} = RN_q^{1/2} 1_{qA_n} = 1_{A_n}` a.e.
  - So for a.e. `x`, `q^{-1}x ∈ A_n ⇔ x ∈ A_n` for every `n`. Hence `q^{-1}x = x` a.e.
  - `T` is countable, so there is a conull `X_0` fixed pointwise by `T`, and hence by `T̄`
    acting through `p`.
- Suppose `β : T̄ × X → R` is measurable, with `β(gh, x) = β(g, hx) + β(h, x)` a.e. for each
  pair and `β(z, ·) = 1` a.e.
  - Intersect the countably many conull sets with `X_0`. The result is non-empty, since
    `μ ≠ 0`.
  - At any point `x` of it, `g ↦ β(g, x)` is a homomorphism `T̄ → R` with `z ↦ 1`. This
    contradicts (P).

## Step 6. Item (E) and the tessellation example

Let `X` be Polish with a jointly continuous `G`-action, and `μ` a `T`-invariant Borel probability.
- **Invariance.** For `f ∈ C_b(X)` and `g_n → g` in `G`, `f(g_n x) → f(gx)` for every `x`. By
  dominated convergence, `g ↦ ∫ f∘g dμ` is continuous on the metrizable group `G`.
  - It is constant on the dense subgroup `T` (Step 1), hence constant on `G`.
  - Borel probabilities on a metrizable space are determined by their integrals of `C_b`
    functions. So `g_*μ = μ` for all `g ∈ G`.
- **Continuity.** The same dominated convergence, with inversion continuous, gives
  `‖f∘g_n^{-1} − f∘g^{-1}‖_2 → 0` for `f ∈ C_b(X)`.
  - `C_b(X)` is dense in `L²(μ)` for a finite Borel measure on a metric space.
  - The Koopman operators are unitary, so `κ` is strongly continuous on `G`, and hence
    `C^0`-continuous on `T`.
- (D) then applies, and `T` fixes `μ`-a.e. point.

**Example.** Identify `S^1` with `RP^1`; any homeomorphism will do.
- `PSL2(R)` is closed in `G`. A divergent sequence of Möbius maps converges pointwise, off one
  point, to a constant map, so it has no uniform limit in `G`. Hence `PSL2(Z)` and any lattice
  `Λ_0`, being discrete in `PSL2(R)`, are closed in `G`.
- So `X = G/Λ_0` is Polish, with a jointly continuous `G`-action.
- A point `gΛ_0` fixed by `T` would give `g^{-1}Tg ≤ Λ_0`. This is impossible: `T ⊃ F ⊃ Z²`, and
  lattices of `PSL2(R)` contain no `Z²`.
- So `G/Λ_0` carries no `T`-invariant probability. In particular the Fuchsian witness of the
  calibration cannot be transplanted to `T` along any circle-functorial construction.

## Scope check

- The only place continuity enters is Step 1 plus (U). Every witness that uses dyadic or
  breakpoint data, for example `T/H` for a discrete `H` or Farley's cubical complex, is
  `C^0`-discontinuous and untouched.
- Sanity: `T` is Haagerup (Farley), and by (C) no proper cnd function on `T` is `C^0`-continuous.
  There is no conflict.
