---
rg: 2
id: thompson-t-amenable-actions-free-off-fixed-points-proof
kind: route
title: Dudko--Medynets character rigidity plus a Hilbert-space averaging argument make the stabilizer IRS trivial, and arc halving absorbs every measure-fixing stabilizer
target: thompson-t-amenable-actions-are-free-off-fixed-points
requires:
  - no-proper-character-groups-avoid-amenable-orbit-full-groups
  - thompson-t-orbits-carry-no-invariant-means
  - mean-free-amenable-actions-residually-amenable-and-sofic
  - elek-szabo-essentially-free-amenable-actions
---

Notation as in the claim. The imports are used as follows.
- `no-proper-character-groups-avoid-amenable-orbit-full-groups`, item 4: `T` has no proper
  characters. Its only indecomposable characters are `1` and `δ_e`.
- `thompson-t-orbits-carry-no-invariant-means`: the formulas for `x_0`, `r_(1/4)`, `r_(1/2)`
  and the three arc identities of its proof.
- `mean-free-amenable-actions-residually-amenable-and-sofic`, items 2 and 3: heredity and soficity.
- `elek-szabo-essentially-free-amenable-actions`: Theorem 3, only for the "test" consequence.

**Step 0: orbits are infinite.** Let `y ∉ Fix T`. Then `Stab(y)` is proper. If the orbit `Ty`
were finite, the normal core of `Stab(y)` would be a proper normal subgroup of finite index. By
simplicity it would be trivial, so `T` would be finite. It is not. So every orbit outside `Fix T`
is infinite. It is connected in the Schreier graph for `S`, so its ball of radius `L` about any
point has at least `L + 1` points.

**Core lemma.** Let `Y` be a `T`-set with `Fix T = ∅` and `n` an invariant mean on `Y`. Then
`n(Fix g) = 0` for every `g ≠ e`.

*Step 1: a Hilbert space.* Let `𝓑` be the space of maps `f : Y → ℓ²(Y)`, `y ↦ f_y`, with
`sup_y ‖f_y‖ < ∞`. Put `⟨f, f'⟩ = n(y ↦ ⟨f_y, f'_y⟩)`. The integrand is bounded, and the form is
positive semidefinite because `n` is positive. Let `𝓗` be the completion of `𝓑` modulo null
vectors, and `[f]` the class of `f`. For `g ∈ T` put `(π(g)f)_y = λ(g)f_y`, where
`(λ(g)φ)(z) = φ(g^(-1)z)` is the unitary permutation representation on `ℓ²(Y)`. Then
`⟨π(g)f, π(g)f'⟩ = ⟨f, f'⟩` pointwise in `y`, so `π` is a unitary representation of `T` on `𝓗`.

Let `ξ_y = δ_y`. Then `‖[ξ]‖ = 1` and `⟨π(g)ξ, ξ⟩ = n(y ↦ ⟨δ_(gy), δ_y⟩) = n(Fix g)`.

*Step 2: the function `χ(g) = n(Fix g)` is a character.*
- It is positive definite and `χ(e) = 1`, because it is the diagonal matrix coefficient of the
  unit vector `[ξ]`.
- It is a class function: `Fix(hgh^(-1)) = h·Fix(g)`, and `n` is invariant.

The characters of `T` form a convex set, compact for pointwise convergence. Its extreme points
are `1` and `δ_e` (import). By Krein--Milman it is the closed convex hull of these two points,
the segment `{s + (1-s)δ_e : 0 ≤ s ≤ 1}`. So `χ(g) = s` for all `g ≠ e`, for some `s ∈ [0,1]`.

*Step 3: an invariant vector with `⟨η, ξ⟩ = s`.* For finite nonempty `A ⊆ T` put
`v_A = |A|^(-1) Σ_(a ∈ A) π(a)[ξ]`. Since `⟨π(a)ξ, π(b)ξ⟩ = χ(b^(-1)a) = s + (1-s)1[a = b]`,
- `⟨v_A, v_B⟩ = s + (1-s)|A ∩ B| / (|A||B|)`;
- `‖v_A - v_B‖² ≤ (1-s)(1/|A| + 1/|B|)`;
- `⟨v_A, ξ⟩ = |A|^(-1) Σ_(a ∈ A) χ(a) = s + (1-s)1[e ∈ A]/|A|`.

Take finite sets `A_k` with `|A_k| → ∞`. The `v_(A_k)` are Cauchy, with a limit `η` that does
not depend on the sequence, and `⟨η, ξ⟩ = s`. Since `π(g)v_A = v_(gA)` and `|gA| = |A|`,
`‖π(g)η - η‖ = lim ‖v_(gA_k) - v_(A_k)‖ = 0`. So `η` is `T`-invariant.

*Step 4: every invariant vector is orthogonal to `ξ`.*

*Pointwise bound.* Let `φ ∈ ℓ²(Y)`, `y ∈ Y`, and `ε = max_(s ∈ S) ‖λ(s)φ - φ‖`. Then
`|φ(sz) - φ(z)| ≤ ε` for all `z` and `s ∈ S`, since `S` is symmetric and `‖·‖_∞ ≤ ‖·‖_2`. So
`|φ(z)| ≥ |φ(y)| - Lε` on the ball of radius `L` about `y`, which has at least `L + 1` points by
Step 0. If `|φ(y)| > Lε`, then `‖φ‖² ≥ (L+1)(|φ(y)| - Lε)²`. In all cases
```text
|φ(y)| ≤ Lε + ‖φ‖ / sqrt(L+1).                                    (PB)
```

*Approximation.* Let `η` be invariant and `δ > 0`. Choose `f ∈ 𝓑` with `‖[f] - η‖ ≤ δ`. Then
`‖π(s)[f] - [f]‖ ≤ 2δ` for `s ∈ S`, and `‖[f]‖ ≤ ‖η‖ + δ`. Put `ε_y = max_s ‖λ(s)f_y - f_y‖`.
By the Cauchy--Schwarz inequality for the positive functional `n`,
- `n(ε_y) ≤ Σ_(s ∈ S) n(‖λ(s)f_y - f_y‖) ≤ Σ_s n(‖λ(s)f_y - f_y‖²)^(1/2) ≤ 2|S|δ`;
- `n(‖f_y‖) ≤ n(‖f_y‖²)^(1/2) = ‖[f]‖`.

Now `⟨[f], ξ⟩ = n(y ↦ f_y(y))`. Apply (PB) to `φ = f_y` at the point `y`:
```text
|⟨η, ξ⟩| ≤ δ + |n(f_y(y))| ≤ δ + L·2|S|δ + (‖η‖ + δ) / sqrt(L+1).
```
Let `δ → 0` and then `L → ∞`. So `⟨η, ξ⟩ = 0`.

*Conclusion.* Steps 3 and 4 give `s = 0`, so `n(Fix g) = χ(g) = 0` for `g ≠ e`. ∎

Invariance of `n` is used only in Step 2. Step 4 uses only that all orbits are infinite. It is the
finitely additive form of "a group all of whose orbits are infinite has no invariant vectors in
`ℓ²` of the orbits".

**Item 1.** `Fix T` is `T`-invariant, and so is `Y = Ω \ Fix T`, which has no global fixed point.
For `g ≠ e`, `Fix g ⊇ Fix T`, so `m(Fix g) = m(Fix T) + m(Fix g ∩ Y)`. If `m(Y) = 0` the last
term is `0`. Otherwise `n = m(· ∩ Y)/m(Y)` is an invariant mean on `Y`, and the core lemma gives
`n(Fix g ∩ Y) = 0`. The IRS statement follows. On `Fix T` the stabilizer is `T`. On `Y`, for each
`g ≠ e`, the stabilizer contains `g` only on a null set. The last bullet is the core lemma
itself.

**Item 2.**
- (a ⇒ b): the core lemma.
- (b ⇒ a): `m(Fix T) ≤ m(Fix s) = 0` for any `s ∈ S \ {e}`, so `Ω \ Fix T` has full mass, and the
  mean restricts to it.
- (c ⇒ a): choose proper `H_k` and finite `P_k ⊆ T/H_k` with
  `Σ_s |sP_k \ P_k| / |P_k| → 0`. On `Ω = ⊔_k T/H_k`, which has no global fixed point, any
  weak*-cluster point of the uniform probabilities on `P_k` is an invariant mean.
- (b ⇒ c): fix `s_0 ∈ S \ {e}` and `0 < ε < 1`. Item 3 of
  `mean-free-amenable-actions-residually-amenable-and-sofic`, with `K = S`, gives a finite
  nonempty `A ⊆ Ω` with `Σ_s |sA Δ A| + |A ∩ Fix(s_0)| ≤ ε|A|`.
  - Let `A' = A \ Fix T ⊇ A \ Fix(s_0)`. Then `|A'| ≥ (1-ε)|A| > 0`.
  - Since `Ω \ Fix T` is invariant, `sA' \ A' ⊆ sA \ A`. So
    `Σ_s |sA' \ A'| ≤ ε|A| ≤ ε/(1-ε)·|A'|`.
  - Split `A'` along its orbits, `A' = ⊔_i A'_i`. Each `sA'_i` stays in its orbit, so
    `Σ_i Σ_s |sA'_i \ A'_i| = Σ_s |sA' \ A'|`. Some `i` therefore has
    `Σ_s |sA'_i \ A'_i| ≤ ε/(1-ε)·|A'_i|`.
  - That orbit is `T/H` with `H` the stabilizer of one of its points, which is proper because
    the orbit misses `Fix T`. So `φ_S(T/H) ≤ ε/(1-ε)`.

Soficity of `T` is item 3 of `mean-free-amenable-actions-residually-amenable-and-sofic`. By its
item 2, the action restricts to a mean-free amenable action of every subgroup, which is then
sofic too. `F ≤ T` as the stabilizer of `0`. A proper co-amenable `H` gives (a) with
`Ω = T/H`, since `Fix T = ∅` there.

**Item 3.** `{x ∉ Fix T : Stab(x) ∩ P ≠ ∅} ⊆ ⋃_(p ∈ P) (Fix(p) \ Fix T)`. Each term is null by
item 1, and `P` is finite. Now let `H < T` be proper and confined by `P`, and suppose `T/H`
carries an invariant mean. `Fix T = ∅` on `T/H`, and `Stab(tH) = tHt^(-1)` meets `P` for every
`t`. So the whole space is null, which is absurd.

**Halving (H).** There is no finitely additive probability `ν` on `𝒜` invariant under `x_0`,
`r_(1/4)` and `r_(1/2)`. The arc identities `x_0[0,1/2) = [0,1/4)`, `r_(1/4)[0,1/4) = [1/4,1/2)`
and `r_(1/2)[0,1/2) = [1/2,1)` are recorded in `thompson-t-orbit-invariant-mean-halving-proof`.
They give:
- `ν[0,1/2) = ν[0,1/4)` and `ν[1/4,1/2) = ν[0,1/4)`;
- so `ν[0,1/2) = ν[0,1/4) + ν[1/4,1/2) = 2ν[0,1/2)`, hence `ν[0,1/2) = 0`;
- `ν[1/2,1) = ν[0,1/2) = 0`, so `ν(S^1) = 0`, a contradiction.

Only finite additivity is used.

**Item 4 (transfer).** Every `g ∈ T` is an orientation-preserving homeomorphism that maps dyadic
rationals to dyadic rationals, so `g[a,b) = [ga, gb)` and `𝒜` is `T`-invariant. Let
`M = {x : Stab(x) fixes a finitely additive probability on 𝒜}`. Since
`Stab(gx) = g Stab(x) g^(-1)` fixes `g_*ν` whenever `Stab(x)` fixes `ν`, the set `M` is
invariant.

Suppose `m(M) > 0`. Choose a representative `y_i` in each orbit contained in `M`, a
probability `ν_i` on `𝒜` fixed by `Stab(y_i)`, and put `ν_(g y_i) = g_*ν_i`. This is well defined
because `Stab(y_i)` fixes `ν_i`, and `ν_(hx) = h_*ν_x` for all `h` and `x ∈ M`. Define
```text
ν̄(E) = m(x ↦ 1_M(x) ν_x(E)) / m(M)        (E ∈ 𝒜).
```
The integrand lies in `[0,1]`, so `ν̄` is a finitely additive probability on `𝒜`. For `h ∈ T`,
`ν_x(hE) = ((h^(-1))_* ν_x)(E) = ν_(h^(-1)x)(E)`. So the integrand for `hE` is `G∘h^(-1)`, where
`G` is the integrand for `E`, using that `M` is invariant. Invariance of `m` gives
`ν̄(hE) = ν̄(E)`. This contradicts (H). So `M` is null.

For a co-amenable `H`, apply this to `Ω = T/H`. If `H` fixed some `ν`, then every
`Stab(tH) = tHt^(-1)` would fix `t_*ν`, and `M` would be all of `T/H`. The three sub-bullets:
- a Borel probability on `S^1` restricts to `𝒜`;
- a finite `H`-invariant set carries the `H`-invariant uniform probability;
- an amenable group of homeomorphisms of a compact metric space fixes a Borel probability
  (Markov--Kakutani / Day).

**Test consequence.** For proper `H`, `T/H` has no global fixed point. By item 1 an invariant mean
on it is mean-free, so co-amenability of `H` is equivalent to condition 1 of Elek--Szabó
Theorem 3 for `T/H`, and hence to its condition 2. ∎
