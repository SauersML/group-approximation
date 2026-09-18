---
rg: 2
id: a2-rs-matrices-irreducible-and-primitive-iff-type-transitive
kind: claim
title: For every group acting freely by type rotating automorphisms on the vertices of a thick Ã₂ building with finitely many orbits, both Robertson–Steger transition matrices are irreducible, and they are primitive exactly when the group is not type preserving (period 3 otherwise), by a local combinatorial argument in the vertex links
distinct_from:
  robertson-steger-a2-boundary-algebras-are-rank-two-ck: that pins Robertson–Steger, who prove irreducibility of each M_i only for PGL_3(K) lattices, K of characteristic zero, through Howe–Moore, and defer the general case to ergodicity results "which will appear elsewhere"; this proves irreducibility and decides primitivity for every building, exotic ones included, with no ergodic theory.
  rs-strip-tail-transitivity-forces-primitive-transition-matrices: that derives primitivity from ergodicity of typed tail-class spaces, which is available only in the linear case; this proves the same conclusion unconditionally.
  cmsz-rs-two-graphs-of-orders-two-and-three-are-primitive: that is a computer certificate for seven explicit groups; this is the general theorem, consistent with it (CMSZ groups are vertex-transitive, hence not type preserving).
artifacts:
  - research/artifacts/gq-bh-bh-groupoid-frontier.md
---

**ESTABLISHED** (lane proof, bh-groupoid 2026-09-18, inline below; not independently
reviewed; no priority claimed).

## Statement

**Setting.**
- `B` is a locally finite thick Ã₂ building. Every panel has `q + 1 ≥ 3` chambers, and the
  vertex links are projective planes of order `q`.
- `Γ` acts on `B` by type rotating automorphisms, freely on vertices, with finitely many
  vertex orbits.
- `θ: Γ -> Z/3` is its type-rotation character.
- `M_1`, `M_2` are the Robertson–Steger transition matrices on `A = Γ\𝔗`
  (arXiv:1302.5593, §7).

**Conclusions.**
1. `M_1` and `M_2` are irreducible. This is Robertson–Steger's (H2) for each colour
   separately, and in particular (H2).
2. If `θ ≠ 0`, then `M_1` and `M_2` are primitive.
3. If `θ = 0`, both have period exactly 3, and their cyclic classes are the base types of
   tiles.

**Consequence.** With `rs-two-graph-aperiodicity-from-h3-and-irreducibility`, the
Robertson–Steger 2-graph `Λ_Γ` is aperiodic for every such `Γ`, and primitive in both
colours when `θ ≠ 0`. This is the corrected form of
`robertson-steger-a2-two-graphs-are-primitive-and-aperiodic`.

## Proof

**Tiles as chamber pairs.** A tile `t` is an ordered pair `(C_0, C_1)` of distinct chambers
sharing a panel `P(t)`, its *diagonal*. `C_0` is the up chamber, containing the base vertex,
and `C_1` is the down chamber.
- The *phase* of `t` is the cotype of `P(t)`, which is the type of its base vertex.
- Every ordered pair of distinct chambers on a panel is a tile. They lie in an apartment,
  and the types fix the orientation.
- Write `π_σ(C)` for the panel of cotype `σ` of the chamber `C`.

**Successors.**
- Let `t = (C_0, C_1)` have phase `τ`. Its horizontal successors are the tiles
  `b = (C_2, C_3)` with `C_2 ∈ π_{τ+2}(C_1) \ {C_1}` and `C_3 ∈ π_{τ+1}(C_2) \ {C_2}`.
- Indeed, the gallery `C_0, C_1, C_2, C_3` then has the panel-cotype word `(τ, τ+2, τ+1)`
  of the model `𝔭_(1,0)`. That word is reduced, and the gallery does not stammer, so it lies
  in an apartment and is a shape-`(1,0)` parallelogram (as in RS Lemma `frWm`).
- So the successor set `S(t)` depends only on `(C_1, τ)`, and the predecessor set `P(b)`
  depends only on the up chamber `C_2` of `b` and its phase.
- Each tile has `q²` successors in `q²` distinct `Γ`-classes, since `γ` sending one to
  another fixes a vertex. The same holds for predecessors.

**Step 1: complete reducibility.** The quotient digraph on `A` (edges `a -> b` when
`M_1(b,a) = 1`) has all in-degrees and out-degrees equal to `q²`. So it has no edges between
distinct strongly connected components.
- For a component with no incoming edges from outside, its outgoing and incoming edge counts
  agree, so it has no outgoing edges either. Induct.
- So every component `𝒞 ⊆ A` is closed under successors and predecessors, and so is its
  preimage `𝒯` in the set of tiles.

**Step 2: diagonal-panel closure.** For a set `𝒯` of tiles, consider two moves:
- **(m1)** if `(C_0, C_1) ∈ 𝒯`, then `(C'_0, C_1) ∈ 𝒯` for every `C'_0 ∈ π_τ(C_1) \ {C_1}`;
- **(m2)** if `(C_2, C_3) ∈ 𝒯`, then `(C_2, C'_3) ∈ 𝒯` for every `C'_3 ∈ π(C_2) \ {C_2}`
  on the same diagonal.

Each move holds when `𝒯` is closed under successors and predecessors: in (m1) the two tiles
share their successor set, and in (m2) their predecessor set.

Starting from one tile with diagonal `P`, the two moves produce every ordered pair of
distinct chambers of `P`. For the pairs with first chamber `C_1`, use a third chamber, which
exists because `|P| ≥ 3`.

Now let `𝒫_σ` be the set of cotype-`σ` panels all of whose tiles lie in `𝒯`.

**Step 3: vertex form of the successor relation.**
- A cotype-`τ` panel is an edge `(v, x)`, with `type v = τ+1` and `type x = τ+2`.
- A chamber on it is `(v, w, x)`, with `type w = τ`.
- The successors of its tiles have diagonals `(w, y)`, where `(v, w, y)` is a chamber and
  `y ≠ x`.

So:
- (F) `(v, x) ∈ 𝒫_τ` implies `(w, y) ∈ 𝒫_{τ+1}` for all such `w, y`;
- (B) the converse direction holds for predecessors.

**Step 4: links.**
1. **At v.** Fix a vertex `v` of type `τ+1`, and let `L_v = {x : (v,x) ∈ 𝒫_τ}`.
   - Let `x ∈ L_v`, and let `w` be adjacent to both `v` and `x`.
   - Apply (F) to get `(w, y)`, for `y ≠ x` adjacent to `v` and `w`. Then apply (B), taking
     `v` itself as the type-`(τ+1)` vertex. This puts `(v, x') ∈ 𝒫_τ` for every `x' ≠ y`
     adjacent to `v` and `w`.
   - Choosing `y ∉ {x, x'}` (possible since `q + 1 ≥ 3`) gives every `x'` adjacent to `v` and
     `w`.
   - So `L_v` is closed under taking the full pencil through any point of any of its lines
     in the projective plane `lk(v)`.
   - Any two lines meet, so `L_v` is empty or everything.
2. **At w.** By (F), if `L_v` is everything then every neighbour `w` of `v` has some
   `(w, y) ∈ 𝒫_{τ+1}`.
   - The same pencil argument in `lk(w)`, using (B) and then (F), gives
     `(w, y) ∈ 𝒫_{τ+1}` for every `y`.
   - Conversely, (B) returns from such `w` to all of its type-`(τ+1)` neighbours.
3. **Connectivity.** The graph of edges between vertices of types `τ` and `τ+1` is connected.
   It is a hexagonal lattice in each apartment, and any two vertices lie in a common
   apartment.

**Step 5: irreducibility.** Take `𝒯` to be the preimage of a component. Step 4 applies:
- Some `L_v` is nonempty, so every `L_v` is everything.
- So `𝒫_τ` contains all cotype-`τ` panels, and `𝒯` contains all tiles of phase `τ`.
- (F) then gives all phases.

So `𝒞 = A`, which proves item 1. For `M_2`, exchange the roles of `w1` and `w2`.

**Step 6: period.** Let `d` be the period of `M_1`, and `F: A -> Z/d` its cyclic class, with
`F(b) = F(a) + 1` on edges. Lift `F` to a `Γ`-invariant function `F̃` on tiles.
1. **F̃ lives on panels.** Moves (m1) and (m2) preserve `F̃`: tiles with the same successors,
   or the same predecessors, have equal `F̃`. So `F̃(t) = u(P(t))`, and
   `u(w, y) = u(v, x) + 1` in the configuration of Step 3.
2. **Pencils.** Fix a pair `v, w`.
   - For `x, x'` adjacent to both, choose `y ∉ {x, x'}`. Then `u(v,x) = u(w,y) − 1 = u(v,x')`.
   - Likewise `u(w, ·)` is constant on the neighbours `y` of the pair.
   - The pencil argument in the links gives `u(v, x) = U(v)` and `u(w, y) = U'(w)`.
3. **Cotype τ+1 edges.** Applying the same step one phase later, `u(w, y)` depends only on
   `y`. So `u` is constant on cotype-`(τ+1)` edges, by connectivity of the graph of edges
   between types `τ` and `τ+2`.
4. **Constants.** So `u ≡ c_σ` on cotype-`σ` panels, with `c_{σ+1} = c_σ + 1`. Going around
   the three cotypes gives `3 ≡ 0 (mod d)`, so `d ∈ {1, 3}`.
5. **Which case.** `F̃(t) = c_0 + phase(t)`.
   - If `d = 3`, `Γ`-invariance of `F̃` forces `θ = 0`.
   - If `θ = 0`, the base type is an invariant that increases by `1` along edges, so
     `3 | d` and `d = 3`.

This proves items 2 and 3. `M_2` is the same, with phase increments of `2`. ∎

## Remarks

- **Consistency.** The result is consistent with the computer certificate
  `cmsz-rs-two-graphs-of-orders-two-and-three-are-primitive`, where CMSZ groups are
  vertex-transitive and all exponents are 4–5. It is also consistent with the
  type-preserving counterexamples of
  `rs-strip-tail-transitivity-forces-primitive-transition-matrices`, item 1.
- **Why it is purely local.** The only inputs are thickness (`q ≥ 2`, used for a third
  chamber on each panel), the projective-plane links, and connectivity of two-type
  subgraphs. Nothing depends on `Γ` beyond freeness, cocompactness and `θ`.
