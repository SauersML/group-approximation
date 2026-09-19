---
rg: 2
id: v-times-tree-boundary-full-groups-are-f-infinity
kind: claim
title: For groups whose Cayley graphs are trees, V times the boundary groupoid of their product is a product of one-sided SFT groupoids, so the master-route host of the rigid end-shift scaffold is F_∞, simple and of type (A)
distinct_from:
  torsion-free-tree-lattices-embed-in-fp-kgraph-full-groups: that embeds torsion-free lattices on products of trees in F_∞ k-graph full groups; this identifies the master-route host G_V × (Λ ⋉ X) of the rigid end-shift scaffold itself with a product of Matui SFT groupoids (involutions allowed), and reads it as an instance of gate E3′.
  a2-lattice-boundary-skew-shifts-are-quantum-rigid: that is the Ã₂ analogue (a finite skew product of the chamber boundary, F_∞ host, rigidity through the necessity theorem); this is the rank-one case, where no skew product is needed.
  v-times-rigid-topologically-free-sft-full-groups-are-fp: that is the open gate E3′ for all rigid minimal topologically free SFTs over finitely presented groups; this proves it for the tree scaffold.
---

**ESTABLISHED** (lane bh-g3-topfree, 2026-09-18). Steps 1 and 2 are an elementary lane proof. The
finiteness input is X. Li, *Left regular representations of Garside categories II*,
arXiv:2110.04505v2, Corollary `cor:ProdGraphs` (second part), read at source in
`$GQ/src/kep/li-garside-II-2110.04505v2.tex`. Not independently reviewed. No priority is claimed: at
the C*-level, boundary crossed products of free groups are classical Cuntz–Krieger algebras
(Spielberg 1991; recalled, not re-read).

## Setting

- For `i = 1, ..., k` (`k >= 1`), `Λ_i` is a group with a finite symmetric generating set `S_i`
  whose Cayley graph `T_i` is a tree of degree `|S_i| >= 3`. Examples: `F_n` (`n >= 2`) with a free
  basis, and free products of copies of `Z` and `Z/2` with their standard generators, such as
  `Z/2 * Z/2 * Z/2`.
- `X_i = X_∂(Λ_i) ⊆ S_i^(Λ_i)` is the end shift of `free-group-boundary-shifts-are-quantum-rigid`. It
  is equivariantly homeomorphic to `∂T_i`, and a point `x` corresponds to the reduced infinite word
  `x(1) x(s_1) x(s_1 s_2) ...` read along its arrows from `1`.
- `Λ = Λ_1 × ... × Λ_k` and `X = X_1 ⊠ ... ⊠ X_k ≅ ∂T_1 × ... × ∂T_k`, with the product coding of
  `quantum-rigidity-is-product-stable`. `T = G_V × (Λ ⋉ X)` on `C × X`.
- `A_i ∈ {0,1}^(S_i × S_i)` is the non-backtracking matrix: `A_i[s, t] = 1` iff `t ≠ s^(-1)`.
- For a `{0,1}`-matrix `A` over an alphabet `S`, `X_A = {(x_j)_(j >= 1) : A[x_j, x_(j+1)] = 1}` is the
  one-sided SFT with shift `σ`. `G_A` is Matui's groupoid: the arrows are the triples
  `(y, k - l, x)` with `σ^k y = σ^l x`, and the product is `(z, m', y)(y, m, x) = (z, m + m', x)`.

## Statement

1. **The boundary groupoid is an SFT groupoid.** `Λ_i ⋉ ∂T_i ≅ G_(A_i)` as topological groupoids.
   `A_i` is irreducible and is not a permutation matrix.
2. **Finiteness.** `T ≅ G_(A_V) × G_(A_1) × ... × G_(A_k)`, where `A_V` is the full 2-shift. So
   `F(T)` is of type `F_∞`.
3. **Host.** `F(T) = A(T)` is simple, contains `Λ`, and its action on the proper nonempty clopen
   subsets of `C × X` is of type (A).
4. **Gate reading.** `X` is a nonempty minimal, topologically free, not free, quantum-rigid SFT over
   the finitely presented group `Λ`. For `k >= 2`, `Λ` is one-ended and non-amenable. Point
   stabilizers embed in `Z^k`. So `X` passes the master route's rigidity gate E2, and the conclusion of
   its topologically free finiteness gate E3′ (`v-times-rigid-topologically-free-sft-full-groups-are-fp`)
   holds for `X`. Nontrivial isotropy does not obstruct finite presentation.

## Proof

**Step 1.** Fix `i` and drop it from the notation.
- **Irreducibility.** Every row of `A` has `|S| - 1 >= 2` ones, so `A` is not a permutation matrix.
  If `t ≠ s^(-1)` then `s -> t` is a step. To reach `s^(-1)` from `s`, pick `u ∉ {s, s^(-1)}`, which
  is possible since `|S| >= 3`. Then `s -> u -> s^(-1)`.
- **Cocycle.** For an end `x` let `r_t(x)` be the vertex at distance `t` from `1` on the ray to `x`.
  Put `c(g, x) = lim_t (|g r_t(x)| - t)`. This equals `b_(gx)(1, g)`, where
  `b_ξ(u, v) = lim_(y -> ξ) (d(u, y) - d(v, y))` is the Busemann function. It uses
  `d(g, g r_t) = t` and the fact that `g r_t(x) -> gx`. Busemann functions satisfy
  `b_ξ(u, w) = b_ξ(u, v) + b_ξ(v, w)` and `b_(hξ)(hu, hv) = b_ξ(u, v)`. So
  `c(hg, x) = b_(hgx)(1, h) + b_(hgx)(h, hg) = c(h, gx) + c(g, x)`.
- **The lag is realized.** Let `g = a_1 ... a_p` be reduced, and `j` the length of cancellation
  between `a_p a_(p-1) ...` and `x_1^(-1) x_2^(-1) ...`, so `j <= p`. Then
  `gx = a_1 ... a_(p-j) x_(j+1) x_(j+2) ...` is reduced. So `σ^(p-j)(gx) = σ^j(x)` and
  `c(g, x) = p - 2j = (p - j) - j`.
- **The map.** Define `Φ(g, x) = (gx, c(g, x), x)`. By the cocycle identity it is a homomorphism
  `Λ ⋉ ∂T -> G_A`, and it is the identity on units.
- **Injective.** Suppose `Φ(g, x) = Φ(g', x)` and put `s = g^(-1) g'`. Then `sx = x` and
  `c(s, x) = 0`. A nontrivial element of `Λ` acts on `T` without fixed vertices. So it is either
  hyperbolic or an involution inverting an edge, and an involution inverting an edge fixes no end. A
  hyperbolic `s` fixing `x` has `x` as an endpoint of its axis, so `c(s, x) = ±ℓ(s) ≠ 0`. Hence
  `s = 1`.
- **Surjective.** Take `(y, k - l, x)` with `σ^k y = σ^l x`. Write `y = v z` and `x = u z` with
  `|v| = k` and `|u| = l`, and put `g = v u^(-1)`. Then `gx = v z = y`. For `t >= l`,
  `g r_t(x) = v z_1 ... z_(t-l)` is a reduced prefix of `y`, so `c(g, x) = k - l`.
- **Homeomorphism.** Take `|w| > |g|`. On the basic bisection `{g} × Z(w)` the cancellation `j` is
  constant, and `Φ` maps it onto the basic bisection `Z(α, w) = {(αz, |α| - |w|, wz)}` of `G_A`,
  where `α = a_1 ... a_(p-j) w_(j+1) ... w_(|w|)`, since `g(wz) = αz` and `|α| - |w| = p - 2j`.
  So `Φ` is a bijection that maps a basis of compact open bisections onto a basis.

**Step 2.**
- `(Λ_1 × Λ_2) ⋉ (X_1 × X_2) ≅ (Λ_1 ⋉ X_1) × (Λ_2 ⋉ X_2)` via `((g, h), (x, y)) -> ((g, x), (h, y))`.
- `G_V`, the groupoid of germs of `V` on `{0,1}^N`, is the groupoid `G_(A_V)` of the full one-sided
  2-shift (the Cuntz groupoid). This is standard and recalled.
- With Step 1 this gives the product decomposition of `T`. Li's Corollary `cor:ProdGraphs`, second
  part, says that the topological full group of a finite product of groupoids of irreducible
  one-sided SFTs, as in Matui's 2015 paper, is of type `F_∞`. `F` depends only on the topological
  groupoid.

**Step 3.**
- `F(T) = A(T)` by `v-times-ample-full-groups-are-generated-by-transpositions`.
- `T` is minimal: its orbits are products of the dense orbits `V c` and `Λ_i ξ_i`.
- `T` is effective, because `Fix((g_1, ..., g_k)) = ∏ Fix(g_i)` is nowhere dense when some
  `g_i ≠ 1` (item (2) of `master-route-needs-only-topological-freeness`).
- So `A(T)` is simple by Nekrashevych's Theorem 4.1 (`nekrashevych-symmetric-and-alternating-full-groups`).
- `λ -> (c, x) ↦ (c, λx)` embeds `Λ`, since topological freeness gives faithfulness.
- The type (A) clopen action is `fp-v-times-minimal-action-full-groups-have-type-a-actions`, which
  needs only minimality and finite presentation.

**Step 4.**
- Quantum rigidity: item 2 of `free-group-boundary-shifts-are-quantum-rigid`, together with
  `quantum-rigidity-is-product-stable` for `k` factors.
- Minimality and topological freeness pass to products.
- The action is not free: an element of infinite order fixes its two ends.
- The Busemann homomorphism `Stab(ξ_i) -> Z` is injective, since its kernel consists of elliptic
  elements fixing an end, and there are none. So `Stab((ξ_i)) ↪ Z^k`.
- For `k >= 2`, a product of two infinite finitely generated groups is one-ended, and `Λ_1 ⊇ F_2` is
  non-amenable. `∎`

## Calibration

- **An independent check of rigidity.** `topologically-free-subshift-full-groups-force-quantum-rigidity`
  applied to item 2 gives a second proof that `X` is quantum rigid and of finite type, by Li's
  finiteness theorem plus the necessity theorem. The direct proof is by monotone chains of
  projections. The two lane arguments are independent and agree.
- **No new Boone–Higman instance.** Every subgroup of `Λ` already embeds in `V`. What is new is the
  status of the gates, not the groups.

## Lesson for general BH

- **Compression codings are one-sided SFT groupoids in disguise.** For a tree group the transformation
  groupoid of the end shift *is* Matui's `G_A`, with the Busemann cocycle as the lag. So for such
  codings the whole E2 + E3′ package of Track A is Matui–Li finiteness theory, and it holds.
- **Free versus topologically free.**
  - In the free form, no instance of E2 + E3 is known over any group: by the necessity theorem, an
    instance would be a rigid free minimal SFT, and none is known.
  - In the topologically free form there are instances: the tree scaffold (here) and the Ã₂ lattices
    (`a2-lattice-boundary-skew-shifts-are-quantum-rigid`).
- **But these instances are finite-state Li codings.** By
  `finite-state-li-coded-full-groups-have-exponential-word-problem`, their subgroups have word problem
  in time `2^(C l^2)`. So the open content of Track A′ is one sharply defined object: a **compression**
  coding, which supplies rigidity and finiteness, that is **not finite-state**, so that it can carry a
  hard input.
