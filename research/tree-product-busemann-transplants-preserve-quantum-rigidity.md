---
rg: 2
id: tree-product-busemann-transplants-preserve-quantum-rigidity
kind: claim
title: Busemann transplants along lattices in products of trees preserve and reflect quantum rigidity and freeness of cone-deterministic spacetimes; this settles the centrality step (C) for every Ã1 x ... x Ã1 building
requires:
  - busemann-transplants-give-free-sfts-on-building-lattices
  - path-folded-sfts-are-quantum-rigid-only-if-the-fibre-is
distinct_from:
  busemann-transplants-of-rigid-z2-sfts-are-quantum-rigid: that poses the up direction for all Euclidean building lattices and leaves the centrality step (C) open; this proves (C) and the up direction for buildings that are products of trees, irreducible lattices included, and leaves the Ã2 case open.
  path-folds-of-rigid-expansive-z2-sfts-are-quantum-rigid: that is the rank-one case over F_n x Z, where the flow is invariant along the Z factor in which the fibre letters sit; here the tiles advance in every tree at once, so no skeleton layer is invariant along the transport, and the acting group may be an irreducible lattice.
  deterministic-time-lifts-inherit-quantum-rigidity: that lifts along a factor that is deterministic in both directions and can never be free over a free space factor; here the tree directions are deterministic only toward a moving end, and freeness is kept.
  quantum-rigid-sfts-over-products-have-a-single-free-branch: that is a necessary structure theorem (one free branch per slab); transplants realise it with the free branch pointing at the end, and this proves they are rigid.
---

**ESTABLISHED** through `tree-product-busemann-transplant-rigidity-proof` (lane bh-invent-04,
2026-09-18; elementary and algebraic lane proof, one adversarial referee PASS (see Referee); no priority claimed). Quantum families
(Q1–Q3) and `D`-quantum rigidity are as in `fp-v-times-subshift-full-groups-force-quantum-rigidity`;
nothing below restricts `dim W` or `char k`.

## Setting

- `T_1, …, T_r` (`r >= 1`) are locally finite trees without leaves, of degree `>= 3` at every vertex.
  `Γ ≤ Aut(T_1) × … × Aut(T_r)` acts simply transitively on `V = V(T_1) × … × V(T_r)`, and `o ∈ V`.
  - `S_i ⊆ Γ` is the set of elements that move `o` along one edge of `T_i`, fixing the other coordinates.
  - `S = ∪ S_i` generates `Γ`. The Cayley graph is the 1-skeleton of the product, and the word metric
    is the `ℓ^1` product metric.
  - Examples: `F_{n_1} × … × F_{n_r}`; every BMW group, i.e. the fundamental group of a finite complete
    square complex with one vertex (`r = 2`), irreducible ones included (Wise's non-residually-finite
    lattices, the Burger–Mozes lattices); the Rattaggi lattices (`r = 3`).
- `Λ_0` is any finitely generated group, possibly trivial. The acting group is `Λ = Λ_0 × Γ`.
- **Skeleton.** For ends `ξ = (ξ_1, …, ξ_r)`, `b_ξ : V -> Z^r` is the vector of Busemann functions,
  normalised by `b_ξ(o) = 0` and increasing toward `ξ_i`. The skeleton symbol at `γ` records, for each
  `i`, the edge of `T_i` along which the vertex `γo` moves toward `ξ_i` (its *arrow*).
- **Fibre.** `Y ⊆ A^(Λ_0 × Z^r)` is an SFT that is **cone-deterministic**: there are a finite
  `W ⊆ Λ_0 × Z_{>=1}^r` and a map `G` with
  `y(λ, z) = G( (y(λw, z + u))_{(w,u) ∈ W} )` for all `y ∈ Y`.
  Every one of the `r` coordinates of every `u` is at least `1`.
- **Transplant.** `Y^Γ ⊆ (Arrows × A)^Λ` is the set of `(ξ, t)` with
  `t(λ, γ) = y(λ, b_ξ(γo))` for some `y ∈ Y`.

## Theorem

1. **Finite type and coding.** `Y^Γ` is an SFT over `Λ`. It is the skew product
   `(∂T_1 × … × ∂T_r) ×_b Y`.
2. **Freeness.** If `γ ≠ 1` fixes `ξ`, its Busemann translation `τ_ξ(γ) ∈ Z^r` is nonzero. So `Λ`
   acts freely on `Y^Γ` whenever `Λ_0 × Z^r` acts freely on `Y`.
   If `Γ = F_{n_1} × … × F_{n_r}` with free bases, freeness of `Y` is also necessary.
3. **Centrality (C).** In every `D`-quantum family for `Y^Γ` with `D > R_W := max_{(w,u) ∈ W} (|w| + |u|_1)`,
   every arrow marginal commutes with every marginal at every site.
4. **Rigidity.** If `Y` is `D_Y`-quantum rigid over `k`, then `Y^Γ` is `D`-quantum rigid over `k` for
   every `D >= max((2r + 1) D_Y, R_W + 1)`.
5. **Converse.** If `Y^Γ` is `D`-quantum rigid over `k`, so is `Y`, by
   `path-folded-sfts-are-quantum-rigid-only-if-the-fibre-is`. The fold is
   `(λ, γ) ↦ (λ, b_ξ(γo))` along one skeleton point; it is 1-Lipschitz and onto.

So a cone-deterministic `Y` is quantum rigid (at some scale) iff its transplant is.

## Corollaries

- **(a) Building lattices of type Ã1 × Ã1.** Let `r = 2`, `Λ_0 = 1`, and let `Y_0` be an
  NE-deterministic `Z^2`-SFT, `y(z) = G(y(z + e_1), y(z + e_2))`. Take `M ∈ GL_2(Z)` with both columns in
  `Z_{>=1}^2`, e.g. columns `(2,1)` and `(1,1)`. Then `Y = Y_0 ∘ M^(-1)` is cone-deterministic, and `Y^Γ`
  is the Busemann transplant of `busemann-transplants-give-free-sfts-on-building-lattices`.
  - For products of trees, (H_Ω) holds, the boundary shift is rigid, and (C) holds by item 3.
  - So the Statement of `busemann-transplants-of-rigid-z2-sfts-are-quantum-rigid` holds, in the form of this Setting, for every lattice acting simply
    transitively on the vertices of a product of two trees.
- **(b) Strongly aperiodic SFTs, unconditionally.** With the Kari–Papasoglu 4-way deterministic
  aperiodic tile set as `Y_0`, every group `Γ` of the Setting with `r = 2` carries a strongly
  aperiodic SFT. This includes `F_m × F_n` and every BMW group. It is quantum rigid **iff** the
  Kari–Papasoglu tiling SFT is. The literature on strongly aperiodic SFTs over BMW groups was not
  searched, so no novelty is claimed for the existence part.
- **(c) Rank one.** For `r = 1` and `Λ_0 = Z` this is the shape of
  `path-folds-of-rigid-expansive-z2-sfts-are-quantum-rigid`: a row that determines the next row down
  is cone-deterministic toward the end. For `r = 1` and any `Λ_0`, a free rigid SFT over `Λ_0 × F_n`
  comes from every free rigid SFT over `Λ_0 × Z` whose `Λ_0`-slice at height `m` determines the slice
  at `m - 1`.
- **(d) Gate G2 over tree-lattice envelopes.** For every `Λ_0` and every `Γ` as above, a free
  quantum-rigid SFT over `Λ_0 × Γ` follows from a free, quantum-rigid, cone-deterministic SFT over
  `Λ_0 × Z^r`. The tree factors add non-amenability and one-endedness (`r >= 2`) at no cost in
  rigidity.

## What stays open

- **Ã2 and higher rank.** The proof uses two features of products of trees:
  - along a geodesic of `T_i`, the arrow events form monotone chains;
  - the arrows of the other trees are invariant under moves in `T_i`.

  In an Ã2 building, the sector germs at a vertex are chambers of a generalised triangle, not arrows.
  The events "`c` projects to this chamber of the link" are not totally ordered along geodesics. The
  sharp remaining question: is there a partition of unity by germ events along `[x, x']` on each piece
  of which either the germ at `x'` is scalar or the tile expansion at `x` strictly approaches `x'`?
  If so, the proof in `tree-product-busemann-transplant-rigidity-proof` goes through verbatim.
- **Minimality** of `Y^Γ` is not claimed.
- **The Z^r gate.** The known rigid `Z^2` inputs, the permutive triangles, have periodic points. The
  known strongly aperiodic cone-deterministic ones (Kari–Papasoglu) have unknown rigidity.
  In the closure of `determinism-closure-certifies-quantum-rigidity`, the four corner rules alone never
  enlarge a square, because a point outside a square has at most one neighbour in it. Other
  determination rules of the Kari–Papasoglu set were not examined.

## Lesson for general BH

- **Trees are transparent to rigidity.**
  - Busemann transplant along any lattice in a product of trees, irreducible ones included, neither
    creates nor destroys quantum rigidity or freeness of a cone-deterministic spacetime.
  - The tree factors supply non-amenability, one-endedness and compression rigidity of the skeleton.
    The fibre's rigidity problem passes through unchanged.
  - So for E2 over any envelope `Λ_0 × Γ`, the whole difficulty sits in a free cone-deterministic
    spacetime over `Λ_0 × Z^r`.
- **Where the mechanism lives.** It is **chain centrality**:
  - skeleton events that form monotone chains along geodesics are central in every quantum family;
  - this holds whenever the decoration is transported toward the end with a strictly positive advance
    in every tree;
  - each piece of the chain either freezes the far arrow or lets the decoration step closer.
- **Consequence for the master route.** A non-amenable factor can create fibre rigidity only through
  geometry whose germ events are not chains, as in Ã2 or other higher-rank geometry. Everything
  tree-like is a change of coordinates.

## Referee (bh-ref-kourovka-a, 2026-09-18): PASS

I checked `tree-product-busemann-transplant-rigidity-proof` line by line.

- **Step 0.** Item 2: a `γ_i` that fixes `ξ_i` with zero translation cannot be hyperbolic, and it
  cannot be an inversion either, since an inversion fixes no end. So it is elliptic and fixes a ray
  pointwise, hence fixes a vertex of `V`, and `γ = 1`.
- **Step 1.** Site independence of `[x → x']`: `γ S_j o` is exactly the set of `T_j`-neighbours of
  `γo`, so the ball-sum argument of the path fold applies along `S_j`- and `Λ_0`-edges.
  - `[x→x'] + [x'→x] = I` holds.
  - `A_(j+1) ⊑ A_j` holds, since two distinct letters at one site are orthogonal.
- **Step 2.** All sites are within `R_W < D`.
- **Step 3, the induction `H_i(n) ⇒ H_i(n+1)`.** It is correct as written.
  - `Σ Q_j = I` telescopes, and each `Q_j` commutes with `M` by `H_i(n)`.
  - Pieces `j < n`: `B_n Q_j = Q_j`, because `A_n ⊑ A_j`. So `PQ_j = [x''=g_n] Q_j`, and
    `[P, Q_j M] = 0`.
  - Piece `n`: `A_n ⊑ A_0,…,A_(U−1)`, because `U <= R_W < 2D <= n`. So the `T_i`-forward path is the
    geodesic. Summing over the other trees' assignments gives
    `A_n T_a = Σ_(σ') A_n e_(σ') Φ^a_σ`.
  - Every tile of `Φ` sits at `T_i`-distance `n + 1 − u_i <= n` from `x'`. This is where
    `u_i >= 1` is used, and `H_i(n)` applies there.
- **Step 4.** Coherence closes by induction, because `u_i >= 1` makes the forward paths merge one
  step sooner.
- **Step 5.** The canonical line is a geodesic with `b_i(ℓ_i(m)) = m`. In (Q3), `e ⊑ e'`, and the
  partial pattern lies within `(2r+1)D_Y <= D`; a realization would contain `α`.
- **Step 6.** `T_a = Σ_z [b(γ)=z] F_a(λ, z)` follows by Step 4, because vertices at one level
  share a forward ancestor.

**Not re-checked:**
- item 5 and the converse, which cite the down-direction fold node;
- Corollary (b)'s Kari–Papasoglu 4-way determinism, which is recalled from the literature;
- the novelty of existence over `F_m × F_n` and over BMW groups, as the node itself says.
