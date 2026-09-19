---
rg: 2
id: end-shift-path-covers-are-rigid-with-one-spine
kind: claim
title: The end shift of F_n codes, by a radius-zero block map, a paradoxical path cover by descending geodesic rays; it is quantum rigid, and its only backward-infinite path is one spine, which exists for finitely many orbits of ends; seeded codings over it are rigid off that spine
distinct_from:
  paradoxical-subshifts-are-never-quantum-rigid: that shows BSS's paradoxical geometry is never rigid, because its colours are free local choices; this supplies a paradoxical path cover with no free choice, read off a rigid shift.
  free-group-boundary-shifts-are-quantum-rigid: that proves rigidity of the end shift; this extracts from it the path and grid geometry of self-simulation, and locates exactly where that geometry has backward-infinite paths.
  path-folded-sfts-are-quantum-rigid-only-if-the-fibre-is: that folds a Z^2 fibre along horoheights of one end; this uses the same flow to index disjoint one-sided grids, as Barbieri–Sablik–Salo do with their paradoxical subshift.
---

**ESTABLISHED (lane bh-g2-fixedpoint-b, 2026-09-18; elementary lane proof, not reviewed; no priority
claimed).** Quantum families are as in `fp-v-times-subshift-full-groups-force-quantum-rigidity`.

## Setting

- `F_n`, with `n >= 2`, has a free basis. `S` is the symmetric basis, with a fixed total order.
- `X_∂ ⊆ S^(F_n)` is the end shift: `x(w) = s` means the arrow at `w` points to `ws`, toward the end
  `ξ(x)`. The *parent* of `w` is `w x(w)`. The *children* of `w` are `ws` for
  `s ∈ S \ {x(w)}`, and their arrows point back to `w`.
- Let `σ_i(w)` be the `i`-th element of `S \ {x(w)}`, and put `ψ_i(w) = w σ_i(w)`, the rank-`i`
  child of `w`.
- **Paths.** `γ_w(0) = ψ_1(w)` and `γ_w(m+1) = ψ_2(γ_w(m))`.
- **Height.** `h(w) = h_ξ(w)` is the horoheight; a child is one lower than its parent.
- **The spine map.** `ν : S → S` sends `s` to the second element of `S \ {s^(-1)}`. `Per(ν)` is its
  set of periodic points.
  - For a cycle `s_0 = ν(s_1), s_1 = ν(s_2), …, s_(p-1) = ν(s_0)` of `ν`, put
    `u = s_0^(-1) s_1^(-1) ⋯ s_(p-1)^(-1)`.
  - Let `Σ_ν ⊆ ∂F_n` be the union of the `F_n`-orbits of the attracting ends `u^(+∞)`, over the
    cycles of `ν`.

## Theorem

1. **Rigid paradoxical cover, no free choice.**
   - `ψ_1` and `ψ_2` are injective with disjoint images, and both are block maps of radius `0` in
     `x`.
   - So is the whole path and grid structure below: which vertex is the rank-`i` child of which, and
     where paths start. It is read off `x`, adding no layer.
   - Over any `Γ_0 × F_n × F_m`, the geometry lives on `pt ⊠ X_∂(F_n) ⊠ X_∂(F_m)`. That shift is
     `D`-rigid for every `D` and every field, by `free-group-boundary-shifts-are-quantum-rigid` and
     `quantum-rigidity-is-product-stable`. It is minimal, and `F_n × F_m` acts topologically freely on it.
2. **Descending disjoint rays.**
   - The paths `γ_w` (`w ∈ F_n`) are pairwise disjoint, and `h(γ_w(m)) = h(w) - 1 - m`.
   - Each `γ_w` is a geodesic ray going down, away from `ξ`.
   - On `F_n × F_m`, the grids `(i, j) ↦ (γ_w(i), γ'_(w')(j))` are pairwise disjoint isometric
     embeddings of `(N^2, ℓ^1)`.
3. **One spine.** The *chain* of a vertex `v` is `v, parent(v), parent^2(v), …`, continued while the
   current vertex is a rank-2 child. Its length `τ(v) ∈ {0, 1, …, ∞}` depends on `x` locally along the
   chain.
   - A chain that ends at a rank-1 child `ψ_1(w)` makes `v = γ_w(τ(v))`, a path point with index
     `τ(v)`.
   - A chain that ends at a child of rank `>= 3` means `v` lies on no path.
   - If `ξ ∉ Σ_ν`, then `τ < ∞` everywhere.
   - If `ξ ∈ Σ_ν`, say `ξ = g u^(+∞)`, then `{τ = ∞}` is exactly one bi-infinite geodesic. This is
     the axis `ℓ_ξ` of `g u g^(-1)`, which reads `… u u …`. Locally it looks like a path, but it has
     no start: it is BSS's bi-infinite path, and here there is at most one.
   - `Σ_ν` is a finite union of `F_n`-orbits, so it is countable. For `n = 2` with
     `a < a^(-1) < b < b^(-1)`, `ν` has the single cycle `(b, a^(-1))`, and `Σ_ν = F_2 · (b^(-1)a)^(+∞)`.
4. **Seeded codings are rigid off the spine.**
   - *Setting.* Let `Z ⊆ (A × C)^(Γ_0 × F_n × F_m)` be an SFT whose base layer contains the geometry
     of item 1. The rest of the base (data, say) is such that hypothesis (B) of
     `causal-depth-localizes-quantum-noncommutativity` holds.
   - *Time-graded causal rule.* The computation layer obeys a causal rule with two properties. Here
     `v'` is the `F_m`-coordinate of a site.
     - All predecessors of the site have `F_m`-coordinate `parent(v')`.
     - The site has predecessors only if `v'` is a rank-2 child.
     In particular, sites whose `F_m`-coordinate is a rank-1 child, which include every grid's bottom
     row, are seeds. So are all sites off the grids.
   - *Conclusion.* The infinite-depth sites of a base point with ends `(ξ, η)` lie in the one sheet
     `Γ_0 × F_n × ℓ_η`, and there are none unless `η ∈ Σ_ν`. Hence every commutator in every
     `D`-family is supported, in the sense of item 2 of that node, on that sheet.
   - *Finite dimension.* In finite dimension, the non-commuting summand `W_∞` has base spectrum inside
     `{η ∈ Σ_ν}`, a countable set of ends.

## Proof

**1.**
- *Injective.* `ψ_i(w) = ψ_j(w')` forces `w = w'`, since both equal the parent of that vertex. It
  then forces `σ_i(w) = σ_j(w)`, so `i = j`. So each `ψ_i` is injective, and `ψ_1`, `ψ_2` have
  disjoint images.
- *Radius zero.* `σ_i(w)` depends only on `x(w)`.
- *Rigidity.* It is the product statement quoted, with the trivial shift `pt` on `Γ_0`.

**2.**
- *Disjointness* is BSS's Lemma `lem:injectivepaths`, verbatim with `ψ_1, ψ_2` in place of their
  arrows. Suppose `γ_w(m) = γ_(w')(m')` with `m >= m'`. Applying `ψ_2^(-1)` `m'` times gives
  `γ_w(m - m') = ψ_1(w')`. If `m > m'`, this lies in both images, which is impossible. So `m = m'`,
  and then `w = w'`.
- *Heights.* Each step goes to a child, so the height drops by one, and a path that always goes to
  children never backtracks.
- *Grids.* A product of two geodesic rays in `(F_n × F_m, d_1 + d_2)` is an isometric copy of
  `(N^2, ℓ^1)`.

**3.** The first two bullets of item 3 restate the definition of `γ_w`, read backwards through
`ψ_2^(-1) = parent`. Let `L = {τ = ∞}`. For `v ∈ L`, write `v_k = parent^k(v)` and
`v_k = v_(k+1) s_k`.
- *The letter condition.* `v_k` is a rank-2 child of `v_(k+1)`. The arrow of `v_(k+1)` is
  `s_(k+1)^(-1)`, so this says `s_k = ν(s_(k+1))` for all `k >= 0`.
- *The letters are periodic.* Such a sequence has every `s_k` in `∩_j ν^j(S) = Per(ν)`. On `Per(ν)`,
  `ν` is a bijection, so `s_(k+1) = ν^(-1)(s_k)`, and the sequence follows a cycle.
- *So `ξ ∈ Σ_ν`.* The ray from `v` reads `s_0^(-1) s_1^(-1) ⋯`, which is reduced because
  `s_k ∈ S \ {s_(k+1)^(-1)}`. So `ξ = v u'^(+∞)` for a rotation `u'` of a cycle word `u`, and
  `v u'^(+∞)` lies in the orbit of `u^(+∞)`.
- *Conversely.* If `ξ = g u^(+∞)`, the ray from `g` reads `u u ⋯`. The same letter computation shows
  that `g` is a rank-2 child of its parent at every step, so `g ∈ L`.
- *`L` is one line.*
  - Take `v, v' ∈ L` with neither an ancestor of the other. Their rays to `ξ` first meet at some
    vertex `q`, entering it through distinct children. Both of those would be rank-2 children of
    `q`, which is impossible.
  - So `L` is totally ordered by ancestry.
  - `L` is closed under `parent` and under `ψ_2`. So it is a single bi-infinite geodesic through `g`,
    namely the axis of `g u g^(-1)`.
- *Finitely many orbits.* There are at most `|Per(ν)|` cycles.
- *Example.* For `n = 2`: `ν(a) = ν(a^(-1)) = b` and `ν(b) = ν(b^(-1)) = a^(-1)`. The one cycle gives
  `u = b^(-1) a`.

**4.**
- *Depth bound.* Each step of a backward causal chain moves the `F_m`-coordinate from a rank-2 child
  to its parent, so it follows the chain of item 3 in the `F_m` factor. Hence the depth of a site is
  at most `τ'(v')`, the chain length of its `F_m`-coordinate for the end `η`.
- *The infinite-depth locus.* A site has infinite depth only if `τ'(v') = ∞`, that is,
  `v' ∈ ℓ_η`. By item 3 this needs `η ∈ Σ_ν`.
- *Conclusion.* Items 2 and 4 of `causal-depth-localizes-quantum-noncommutativity` give the claim.
  The ends `(ξ, η)` of a base spectrum point are read off its `X_∂` letters. ∎

## What this does and does not give for Track A

- **What it gives.** A way to build BSS-style self-simulation on a Track A square that keeps the
  geometry rigid.
  - Enlarge the envelope to `Λ_1' = Λ_1 × F_n`. It is still finitely presented, decidable and
    non-amenable, and it contains `K`.
  - Take `Δ = F_n × F_n ≤ Λ_1'^2`. It is a direct factor, so it is a mediated subgroup in BSS's
    sense (their section `sec:stability_properties`).
  - Put the grids in `Δ`, using this geometry.
  - Then E2 for any time-graded seeded coding on this geometry is exactly E2 on one sheet over the
    countably many ends `η ∈ Σ_ν`.
- **What it does not give.** Minimality.
  - Off the spine, a seeded coding computes everything from the base. That is the situation of
    design constraint 1 of `nonamenable-products-have-minimal-sft-extensions-of-free-inputs` (a
    sketch there), under which minimality forces the input to be of finite type. So seeded codings
    over this geometry are not expected to be minimal. Hierarchical codings have infinite depth
    everywhere, and this node says nothing about them.
  - So for the *minimal* E1 ∧ E2 object, infinite depth must occur on a rich set of configurations,
    not only over the countable set `Σ_ν`. Each infinite-depth region must then be unsplittable, by
    the kill test of `causal-depth-localizes-quantum-noncommutativity`.
  - The concrete question left for seeded codings is: on the sheet `Γ_0 × F_n × ℓ_η`, is the
    unseeded computation unsplittable?

## Lesson for general BH

Self-simulation needs paradoxical geometry, and quantum rigidity forbids free local choices. Both are
met by one object: the flow toward an end of a free factor. It is paradoxical (every vertex has
`2n - 1` children), rigid, and its path cover is a radius-zero code.
- **The whole E2 cost of a seeded coding** over this geometry sits on one explicitly known spine
  sheet, over countably many ends. It is not spread through the grids.
- **The design problem shrinks.** From "make a simulation rigid" it becomes "make the computation on
  one backward-infinite sheet unsplittable".
- **The tension with minimality** is now sharp. Minimality needs that sheet to be rich, and rigidity
  needs it to be coupled.
