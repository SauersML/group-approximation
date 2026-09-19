---
rg: 2
id: flagged-pointed-cube-category-proof
kind: route
title: Promises propagate like crossings (leaving and persistence lemmas), labels join by union at median joins, maximal characters are Roller points, and the mismatch sets M_plus and M_minus are absorbed by one flag on each side
target: flagged-pointed-cube-category-resynchronizes-cubulated-actions
requires:
  - pointed-cube-bisection-locus-is-the-regular-boundary
  - pointed-cube-categories-are-li-garside-categories
---

**Lane proof, not independently reviewed.** Notation and the two lemmas are those of
`pointed-cube-bisection-locus-proof` §2:
- **Leaving.** A geodesic that leaves the carrier of `J` never returns.
- **Persistence.** A crossed wall that is not adjacent stays non-adjacent.

Recall `π(σ;w,u) = (σ ∪ H(w,u)) ∩ adj(u)`.

## 0. Composition

**Lemma C.** Let `(w,σ; u,τ)` be a morphism, and let `p_0 = u, …, p_k = u'` be an edge path
with `H(u,u') ∩ τ = ∅`. Then:
1. `H(u,u')` is disjoint from `σ ∪ H(w,u)`. So `w → u → u'` is geodesic and never crosses
   `σ`.
2. `π(τ; u,u') ⊇ π(σ; w,u')`.

*Proof.*
1. Let `J ∈ σ ∪ H(w,u)` be the first wall of that set crossed by the path, at the edge
   `p_{i−1} p_i`. Then `p_{i−1}` is adjacent to `J`, and `w → p_{i−1}` is geodesic and
   crosses no wall of `σ`.
   - If `J` is adjacent to `u`, then `J ∈ π(σ;w,u) ⊆ τ`. But the path avoids `τ`.
   - If `J` is not adjacent to `u`, then `p_{i−1}` is not adjacent to `J`. For `J` crossed
     this is persistence. For `J ∈ σ`: the path left `J`'s carrier by crossing some `K`,
     which it never recrosses; this is leaving.

   Either way we have a contradiction.
2. A wall of `σ ∪ H(w,u)` that is adjacent to `u'` is adjacent to `u`, by the same two
   lemmas. So it lies in `τ`. Walls of `H(u,u')` adjacent to `u'` lie in `π(τ;u,u')` by
   definition. ∎

So composition is well defined and associative.

## 1. Li's hypotheses (item 1)

**Cancellation, units, (F).**
- A morphism with a fixed target representative is determined by its endpoint `(u,τ)`.
  Freeness makes representatives unique up to `G`. So `C⁺_X` is left and right
  cancellative.
- A morphism `(w,σ;w,σ')` is invertible only if `σ' = σ`. So units are trivial, and (F)
  holds.

**Right Noetherian.** A proper right divisor either shortens `H(w,u)` or enlarges the start
label inside the finite set `adj(w)`.

**Lcms.** Take `a_i = (w,σ; u_i,τ_i)`.
- **When there is a common multiple.** Some multiple exists iff `τ_1 ∩ H(w,u_2) = ∅`,
  `τ_2 ∩ H(w,u_1) = ∅`, and `u_1, u_2` have a median join `j` over `w`, with
  `H(w,j) = H(w,u_1) ∪ H(w,u_2)`.
  - The label conditions are necessary: a common multiple crosses `H(w,u_2) ∖ H(w,u_1)`
    after `u_1`.
  - The join condition is necessary as in the unflagged case.
- **The lcm.** It is `(j, τ_j)` with `τ_j = π(τ_1;u_1,j) ∪ π(τ_2;u_2,j)`. Given another
  multiple `(u,τ)`:
  - `j ∈ I(w,u)`;
  - `H(j,u)` avoids `τ_j`, because it avoids `τ_i` and `H(u_i,j)`;
  - `π(τ_j; j,u) ⊆ π(τ_1;u_1,u) ∪ π(τ_2;u_2,u) ⊆ τ`.

  So `(j,τ_j)` divides `(u,τ)`.
- Hence the category is finitely aligned with lcms, and in particular has disjoint mcms.

**Garside family.** Let `𝔖⁺` be the one-step morphisms: `u` is the far corner of a cube `c`
at `w` whose walls avoid `σ` (the 0-cube allowed), with any label `τ ⊇ π(σ;w,u)`, and not
the identity.
- **Local finiteness.** `𝔖⁺` is locally finite (finitely many cubes and labels at each
  object), and generates.
- **Right divisors.** `𝔖⁺^♯` is closed under right divisors, since those are opposite
  faces with labels.
- **Right lcms.** Two one-step morphisms with a common multiple have cube walls that are
  pairwise crossing walls adjacent to `w`. Two disjoint walls adjacent to `w` have disjoint
  far halfspaces, so no vertex lies beyond both. So the lcm is again one step.
- **Full write-up.** The complete verification for referees, using Dehornoy's mcm criterion, an explicit
  normal form and the norm, is `flagged-pointed-cube-garside-verification`. The two bullets below are
  the original sketch.
- **Heads.** The `𝔖⁺`-left-divisors of `a` form a finite set closed under lcm, so `a` has a
  head: the first Niblo–Reeves cube, labelled by every wall that is adjacent there, not
  crossed later, and in `τ` if still adjacent at `u`. Iterating heads gives normal forms
  satisfying Li's normality.
- **Norms.** A label enlargement at `u` is absorbed into the last factor. So
  `‖a‖ = max(height of H(w,u), [a is a pure flag])`. Left divisors have smaller height, so
  `(𝔖⁺^{≤L})^♯` is closed under left divisors.

## 2. Boundary (item 2)

As in §1 of `pointed-cube-bisection-locus-proof`, points of the base cone are directed
hereditary sets `D` of morphisms `o → (z,σ)`.
- **`D` refines its Roller point.** Let `ω_D` be the Roller point of the vertices of `D`.
  Then `D ⊆ D_ω`. If `ω_D` crossed some `J ∈ σ` for `(z,σ) ∈ D`, an element of `D` beyond
  that crossing would have no common multiple with `(z,σ)`.
- **`D_ω` is directed** by the lcm formula, so it is a character.
- **`D_ω` is maximal.** Suppose `D' ⊋ D_ω`, so that `ω' = ω_{D'}` has
  `H(o,ω') ⊋ H(o,ω)`.
  - Take `J ∈ H(o,ω') ∖ H(o,ω)` minimal. Every wall separating `o` from `J` lies in
    `H(o,ω)`.
  - So the gate vertex `p'` next to `J` lies in `I(o,ω)` and is adjacent to `J`.
  - Then `(p', Max(o,p') ∪ {J}) ∈ D_ω ⊆ D'` forbids `ω'` from crossing `J`, a
    contradiction.
- **The maximal points (corrected after bh-ref-q115-b).** A maximal `D` is either principal
  or not. A principal maximal `D = ↓x` needs `x` to have no proper extension, which forces the
  full label `adj(z)`, so `D` is an isolated sink point. A non-principal maximal `D` refines
  `D_{ω_D}` with `ω_D` in the Roller boundary, so `D = D_{ω_D}`. The earlier version of this
  step missed the sinks.
- **Topology.** `ω ↦ D_ω` is continuous and injective, because membership of `(z,σ)` is a
  finite set of halfspace conditions. It is defined on the compact space `∂_R X`, so it is
  a homeomorphism onto a closed set. That set is `X_∞ = ∂Ω ∩ Ω_∞` intersected with the base
  cone.
- **Sinks.** The sinks accumulate only at points `D_ω`, which are limits of `↓(z_n, adj z_n)`
  along rays. So `∂Ω = X_∞ ⊔ {sinks}`, with `X_∞` closed.
- **Invariance.** Prefixing and un-prefixing preserve maximal infinite characters, so `X_∞`
  is invariant. All of §3 takes place on `X_∞`, and there `𝒢⁺` means `I_l ⋉ X_∞`.
- **Other cones.** The cone of `[(w,σ)]` is treated the same way inside `Q(w,σ)`.

## 3. Every element is a bisection (item 3)

Fix `g` and `ω`, a geodesic ray `z_n → ω`, `κ_n = Max(o,z_n)` and `F_g = H(g^{-1}o,o)`.
- **The mismatch sets.**
  - If `gJ ∈ M_+`, then `gJ ∈ H(o,gz_n) = H(o,go) Δ gH(o,z_n)` and `J ∉ κ_n`. Adjacency
    rules out `J ∈ H(o,z_n)`, so `J ∈ F_g ∖ H(o,z_n)` with `J` adjacent to `z_n`.
  - Symmetrically, `gJ ∈ M_-` gives `J ∈ F_g ∩ κ_n`.
- **Choice of `n`.** `F_g` is finite. So for `n` large, `ω` crosses no wall of `F_g` after
  `z_n`.
- **The neighbourhood.** Put `λ = [o→(z_n, κ_n ∪ g^{-1}M_+)]` and let `U` be its cylinder
  intersected with `{ω' : H(z_n,ω') ∩ F_g = ∅}`. `U` is a clopen neighbourhood of `ω`.

**Where `g` sends `U`.** For `ω' ∈ U`:
- **Hyperplanes of `gω'`.** `H(o,gω') = H(o,go) Δ (gH(o,z_n) ⊔ gH(z_n,ω'))`. Since
  `gH(z_n,ω') ∩ H(o,go) = g(H(z_n,ω') ∩ F_g) = ∅`, this equals
  `H(o,gz_n) ⊔ gH(z_n,ω')`. So `gz_n ∈ I(o,gω')`, and the future of `gω'` after `gz_n` is
  the `g`-image of the future of `ω'` after `z_n`.
- **The target label.** That image avoids `g(κ_n ∪ g^{-1}M_+) = gκ_n ∪ M_+`. This set
  contains `Max(o,gz_n) = (gκ_n ∖ M_-) ∪ M_+`, and it equals `Max(o,gz_n) ∪ M_-`.
- **Conclusion.** `(gz_n, gκ_n ∪ M_+) ∈ D_{gω'}`, so `gω' = μw` where
  `μ = [o→(gz_n, Max(o,gz_n)) ] · ε_{M_-}`, `w` is the future of `ω'`, and
  `d(μ) = g·d(λ) = d(λ)`.

So `g|_U` is the prefix replacement `λw ↦ μw`. By compactness `g` is a finite union of
such pieces, which is a global compact open bisection of `𝒢⁺` reduced to the base cone. ∎

## Lesson for general BH

The repair needed exactly one new kind of generator: a flag, a morphism that changes no
position and only strengthens a promise. That is the general move for resynchronization.
When two codings of the same point disagree only about constraints the point satisfies
anyway, add promise-strengthening morphisms. Heads, lcms and normal forms survive, because
promises propagate by the same leaving and persistence lemmas as crossings.
