---
rg: 2
id: a2-lattice-boundary-skew-shifts-are-quantum-rigid
kind: claim
title: Every cocompact lattice of a thick Ã2 building carries a minimal, topologically free, quantum-rigid SFT, obtained by transferring finite presentation of its boundary full-group host through the necessity theorem
distinct_from:
  euclidean-building-boundary-shifts-are-quantum-rigid: that asks for quantum rigidity of the chamber-boundary shift X_Ω itself; this proves it for a finite skew product P of X_Ω, and leaves X_Ω itself open.
  thick-building-flat-sfts-are-never-quantum-rigid: that codes the building over its translation lattice Z^d, where rigidity always fails; this codes the boundary over the lattice itself, where rigidity holds.
  a2-lattices-embed-in-fp-simple-groups: that builds the finitely presented simple host; this reads the host backwards, as a certificate of two-sided rigidity for a subshift over the lattice.
  quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products: that turns rigidity into a finitely presented crossed product; this supplies the rigid input, over a Kazhdan group.
---

**ESTABLISHED** (lane proof; bh-invent-12, 2026-09-18; not independently reviewed; no priority
claimed). It is conditional on the host theorem `a2-lattices-embed-in-fp-simple-groups` (a lane proof
whose Ã₂ link theorem passed bh-verify-master) and on the comparison lemma
`degree-category-full-groups-stabilized-have-type-a-actions` (a lane proof).

## Statement

Let `B` be a locally finite thick Ã₂ building, `Γ ≤ Aut(B)` discrete, cocompact and type rotating,
and `Ω` its space of chambers at infinity. Then there are:
- an integer `n ≥ 1`;
- a finite abelian group `Φ` (the phase group `Z²/nZ²`, or `L/nZ²` in the type-preserving case);
- a continuous cocycle `c̄ : Γ × Ω -> Φ` (the lag of Step 1, mod `n`);
- a nonempty `Γ`-invariant clopen `P ⊆ Ω × Φ`, where `γ(ω, φ) = (γω, φ + c̄(γ, ω))`,

such that:
1. `Γ ↷ P` is minimal and topologically free, and `P -> Ω` is a finite-to-one factor map;
2. `F(G_V × (Γ ⋉ P))` is finitely presented, indeed of type `F_∞`, and simple;
3. `P` is conjugate to an SFT over `Γ` that is `D`-quantum rigid over every field for all large `D`;
4. `LC(P, k) ⋊ Γ` is finitely presented over every field `k`
   (`quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products`, which needs no freeness).

**Instances.** Every CMSZ group, the Tits–Ronan and Ronan–Kantor–Essert lattices (exotic ones
included), and cocompact lattices in `PGL_3` over division algebras over local fields. These groups
are finitely presented and non-amenable. Being cocompact lattices in a 2-dimensional building they are
one-ended, and they have property (T) (Cartwright–Młotkowski–Steger for Ã₂; recalled, not re-read).

So gate G2 of `research/artifacts/gq-bh-synthesis-master-route.md` has a positive answer over a
**one-ended, non-amenable, Kazhdan** group, in the **topologically free** form.

## Proof

Notation is that of `a2-lattices-embed-in-fp-simple-groups` (Steps 1–5).

**Step 1 (the host groupoid is a transformation groupoid).** Let `𝒢_Γ^D` be the amplified groupoid of
Step 3 there, on `⊔_(d ∈ D) 𝒮_(a(d)) ≅ Ω`, with `Ω(d) ≅ 𝒮_(a(d))` via `ω -> g_d^(-1)[O, ω)`.
- An arrow from `Ω(d)` to `Ω(d')` is `(S', n, g, S)` with `S = g_d^(-1)[O, ω)`,
  `S' = g_(d')^(-1)[O, ω')` and `S'(l+n) = g S(l)` for large `l`.
- Put `γ = g_(d') g g_d^(-1)`. Then `[O, ω')` and `γ[O, ω)` share a subsector, so `ω' = γω`.
- Conversely, for `(γ, ω)`, the sectors `[O, γω)` and `[γO, γω)` share a subsector. This gives a lag
  `n = c(γ, ω)`, and it is unique because an isometric quarter-plane embedding satisfies no
  `S'(l+n) = S'(l+n'')` with `n ≠ n''`.
- So `(γ, ω) <-> (S', c(γ, ω), g_(d')^(-1) γ g_d, S)` is a bijection `Γ ⋉ Ω -> 𝒢_Γ^D`. Basic bisections
  correspond (a cylinder times a fixed `γ`), so it is an isomorphism of ample groupoids.
- `c : Γ ⋉ Ω -> Z²` is a continuous cocycle; this uses composition of arrows, `n + n'`.
- **The unamplified groupoid.** The same computation, with the base tiles `i_a` of the tile classes
  `a ∈ A` in place of `D`, identifies `𝒢_Γ` with a clopen reduction of `(Γ ⋉ Ω) × R_A`. Here `R_A`
  is the pair groupoid on the finite set `A`: an arrow from `𝒮_a` to `𝒮_b` is a pair `(γ, ω)` with
  `ω ∈ Ω_a` and `γω ∈ Ω_b`, for clopen sets `Ω_a ≅ 𝒮_a`.
- **Absorbing `R_A`.** `G_V × R_A ≅ G_V`. A complete binary prefix code `p_1, …, p_(|A|)` gives
  `⊔_a C -> C`, `(a, w) -> p_a w`, which conjugates `G_V × R_A` onto `G_V` (the groupoid of
  `V_(2,|A|) ≅ V`). So `G_V × 𝒢_Γ` is a clopen reduction of `G_V × (Γ ⋉ Ω)`.

**Step 2 (the rescaled groupoid is a reduction of a skew product).** The rescaled groupoid
`𝒢_Γ^(n)` of Step 5.1 there consists of the arrows whose lag lies in `nZ²`. In the type-preserving
case lags lie in `L`, and one takes phase 0 in `L/nZ²`. Every arrow with such a lag factors through
prefixes of degrees in `nN²`.
- Let `X'' = Ω × Φ` with the skew action `γ(ω, φ) = (γω, φ + c̄(γ, ω))`.
- Then `(Γ ⋉ X'')|_(Ω × {0}) = {(γ, ω) : c̄(γ, ω) = 0}`, which is the rescaled groupoid in the
  coordinates of Step 1. The lag is the same cocycle after amplification, so the rescaling commutes
  with Step 1's reductions.
- With Step 1's absorption of `R_A`, the host of Step 5.2–5.3 is therefore
  `ℋ = (G_V × (Γ ⋉ X''))|_(Y*)` for a nonempty clopen `Y* ⊆ C × (Ω × {0})`, the image of the object
  cylinders `Y`. Here `G_V = G_2` is the Cuntz groupoid on `C = {0,1}^N`.
- `F(ℋ)` is of type `F_∞` (Step 5.3 there, Li `thm:deg`) and simple (Step 5.6 there).

**Step 3 (one minimal piece).** `Γ ↷ Ω` is minimal (Step 5.4 there). `X'' -> Ω` is a skew-product
extension by a finite group, so every point of `X''` is almost periodic. Hence `X''` is a disjoint
union of finitely many minimal sets. Each is clopen, since its complement is a finite union of the
others. So the minimal invariant clopen sets of `G_V × (Γ ⋉ X'')` are the sets `C × P_i`, one for
each minimal piece `P_i`. `ℋ` is minimal (Step 5.4 there), so `Y* ⊆ C × P` for a single minimal
piece `P`.

**Step 4 (the host is the full group of G_V × (Γ ⋉ P)).** Put `𝒦 = G_V × (Γ ⋉ P)`, which is
minimal. Then `ℋ = 𝒦|_(Y*)`, because `C × P` is invariant.
- **Comparison inside `Y*`.** `F(ℋ)` is finitely presented. So by item 1 of
  `degree-category-full-groups-stabilized-have-type-a-actions`, any two nonempty clopen subsets of
  `Y*` are equivalent by compact open bisections of `ℋ`. `Y*` is a single piece, since `ℋ` is
  minimal.
- **Moving `C × P` into `Y*`.** Every `𝒦`-orbit meets the nonempty open set `Y*`. By compactness,
  `C × P = ⊔_(j=1)^N W_j` with clopen `W_j` and compact open bisections `U_j` of `𝒦` with source
  `W_j` and range inside `Y*`.
- **Disjoint targets.** Split `Y*` into disjoint nonempty clopen sets `Y_1, …, Y_N`. By comparison each
  `Y_j ~ Y*` through a bisection `V_j`. The products `V_j U_j` have sources `W_j` and pairwise disjoint
  ranges inside `Y_j`. Together they give a bisection from `C × P` onto a clopen `Z ⊆ Y*`.
- **Conclusion.** `Z ~ Y*` by comparison, so `C × P ~ Y*`. Conjugating by that bisection gives
  `𝒦 ≅ 𝒦|_(Y*) = ℋ`, and so `F(𝒦) ≅ F(ℋ)`, which is `F_∞` and simple. This is item 2.

**Step 5 (dynamics and coding).**
- **Topological freeness.** `Γ ↷ Ω` is topologically free: aperiodic sectors are dense by Step 5.5
  there, and Ciobotaru–Le Bars (arXiv:2601.13092) give it too. `π : P -> Ω` is open, being the
  restriction of a product projection to a clopen set, and equivariant. If `Fix_P(g)` contained an open
  `U`, then `π(U)` would be open inside `Fix_Ω(g)`, forcing `g = 1`.
- **Coding.** `Ω` is conjugate to the chamber-germ subshift `X_Ω`
  (`euclidean-building-boundary-shifts-are-quantum-rigid`). `c̄` is locally constant, so
  `(ω, φ) -> (γ -> (x_ω(γ), phase of γ^(-1)(ω, φ)))` conjugates `P` to a subshift over `Γ`.

This gives item 1.

**Step 6 (rigidity).** `F(𝒦) = A(𝒦)` (`v-times-ample-full-groups-are-generated-by-transpositions`)
contains every translation `t_s`, every site-conditioned 3-cycle `e_a`, and `V × {1}`. It is finitely
presented, and `Γ ↷ P` is topologically free. So
`topologically-free-subshift-full-groups-force-quantum-rigidity` makes `P` an SFT that is `D`-quantum
rigid over every field for all large `D`. This is item 3, and item 4 follows. `∎`

## What stays open

- **`X_Ω` itself.** Rigidity is proved for the finite skew product `P`, not for `X_Ω`. The skew
  product is needed only because Li's theorem needs loops; rescaling adds the phase coordinate. For
  rank one, `free-group-boundary-shift-is-quantum-rigid` proves the unskewed shift rigid directly.
- **Freeness.** `P` is only topologically free: elements translating a periodic flat fix points of
  `P`. Gate (★) of the master route asks for a free SFT, and
  `free-action-leavitt-tensor-hosts-have-trivial-k1-k2` assumes freeness. Either the ring-side gates
  must accept topological freeness, or `P` must be coupled with a free factor. Uncoupled products
  cannot help: `quantum-rigidity-is-product-stable` makes a product free only if both factors are.
- **Programmability.** `P` lives over the fixed lattice `Γ`, and its host has exponentially bounded
  word problem (finite unit groups). To host a general decidable input the rigid geometry must be
  coupled with a programmable factor `Λ_0`.

## Test against the filters

- **Rank-one locality** (`rank-one-cone-hosts-put-fw-groups-in-local-map-groups`). The cones of this
  host form a 2-graph, not a tree, which lies outside that node's scope. The Kazhdan group `Γ` sits in
  the host globally, as translations, not inside a local-map group. This is consistent with the node.
- **Kazhdan filter** (`decidable-host-classes-reduce-to-canonical-kazhdan-groups`). The host contains
  the infinite Kazhdan group `Γ`, so it is not in any excluded class (amenable, Haagerup, residually
  finite, or finite-Kazhdan).

## Lesson for general BH

**Finite presentation is a rigidity certificate.**
- Read the necessity theorem backwards. Every finitely presented V-stabilized full group of a
  topologically free boundary action is, after the Kakutani bookkeeping of Steps 1–4, a certificate
  that the boundary subshift is quantum rigid.
- The one-sided Li codings that put building lattices into `B_A` therefore also solve the two-sided
  rigidity gate G2 over those lattices. The branching that kills flat codings becomes compression in
  the one-sided coding, and compression, transported to the lattice, becomes rigidity.
- So the rigid objects exist over one-ended Kazhdan groups. What remains between them and the master
  route is **freeness** and **programmability**, not rigidity.
