---
rg: 2
id: clique-union-raag-roller-hosts-are-f-infinity
kind: claim
title: For a free product of at least two free abelian groups (a RAAG whose graph is a disjoint union of cliques, e.g. Z^2 * Z), the V-stabilized full group of the Roller boundary action is of type F_infinity, via a Thumann operad of orthant tiles and coordinate peels; E3' holds for the one-edge case of the cubulated route
distinct_from:
  cocompact-tree-end-shift-hosts-are-f-infinity: that is the edgeless case (trees, one split per tile); this adds flats, where a tile has one peel per coordinate of its cube and the tiles form a Brin-Thompson-like product system glued along a tree.
  raag-cube-codings-fail-li-multiplicity-at-every-power: that shows Li's multiplicity condition (t<d) fails for RAAG cube codings at every power; this avoids (t<d) altogether, since the V factor makes the operad color-tame (Thumann), which is the loop-richness Li needs.
  greedy-cube-codings-make-cubulated-hyperbolic-groups-rsgs: that uses greedy (normal) cube paths to make cubulated hyperbolic groups contracting RSGs; this uses the same normal cube paths as the uniform refinements of a finiteness proof for a host with flats.
  special-cube-complex-groups-lie-in-fp-members-of-class-c: that reduces the cubulated route to E3' and records it as open whenever the graph has an edge; this proves E3' when the graph is a disjoint union of cliques, and isolates the lemma needed for general graphs.
---

## Proposed dependency record (not an accepted route)

The following rejected claim-level metadata is preserved verbatim as a
proposed dependency record. It is not a compiled route, does not establish
this claim, and requires individual mathematical review before any route
is accepted. The historical mathematical prose below is unchanged.

```yaml
requires:
  - special-cube-complex-groups-lie-in-fp-members-of-class-c
  - cocompact-tree-end-shift-hosts-are-f-infinity
  - roller-compactifications-of-cube-complexes-are-sfts
```

**ESTABLISHED** (lane proof, bh-one-relator, 2026-09-19; not reviewed; no priority claimed). The finiteness
input is Thumann's Theorem `41762` (arXiv:1409.1085; definitions `81202`, `79040`, `13449`, `24121`, `26536`,
`77101`, read in the LaTeX source on MSI at `gqsrc/bh-invent-07/thumann.tex`, l.1892–2100 and l.2640–2670).
Everything else is elementary cube-complex geometry, proved below. **Referee requested.**

## Setting

- `Λ = A_1 * ⋯ * A_k` with `k ≥ 2` and `A_i = Z^(n_i)`, `n_i ≥ 1`. This is the RAAG `A_Γ` on a disjoint union
  `Γ` of `k` cliques. Instances: `Z^2 * Z` (one edge plus the route's free vertex `v`), `Z^n * Z`, and free
  groups (`n_i = 1`).
- `X̃` is the universal cover of the Salvetti complex. It is a **tree of flats**:
  - each coset `gA_i` spans a flat `F ≅ R^(n_i)`, cubulated by `Z^(n_i)`;
  - each vertex lies in exactly one flat of each factor, and two flats meet in at most one vertex;
  - the incidence graph of vertices and flats is a tree.

  Every hyperplane lies in one flat, as a coordinate hyperplane.
- `∂ = ∂_R X̃` is the Roller boundary (non-principal ultrafilters), and `F = F(G_V × (Λ ⋉ ∂))`. It is a Cantor
  set, since every tile splits (§2). `Λ` acts topologically freely: an element fixing a tile pointwise fixes the
  hanging tiles inside it setwise, hence their apexes (a box determines its apex), and vertex stabilizers are
  trivial.
- For a flat `F` with `n` coordinates, `F̄ = (Z ⊔ {±∞})^n` is its Roller compactification. Restricting an
  ultrafilter to the hyperplanes of `F` gives a continuous **projection** `π_F : ∂ → F̄`. Here `π_F(U)` is a
  lattice point `v` exactly when `U` leaves `F` at `v` into another flat through `v`.

## Theorem

1. `F` is of type `F_∞`. In particular it is finitely presented, so E3′ holds for `(Λ, ∂)`.
2. **The cubulated route, one edge.** For `Λ = Z^2 * Z = A_(Γ⊔{v})` with `Γ` one edge, and more generally for
   `Γ` a disjoint union of cliques, the one open gate of `special-cube-complex-groups-lie-in-fp-members-of-class-c`
   is closed. That node identifies its SFT `X` with `∂_R` by a Remark, which is a lane observation and not
   refereed. Granting it, the rigid-SFT route to (P)BH runs end to end for every subgroup of `A_(Γ⊔{v})`.

   The inputs reached are subgroups of free products of free abelian groups. These already satisfy BH, so this
   is calibration: a type (A) host with flats, not a new BH case.

## The mechanism in one paragraph

- **Tiles.** Take a vertex `z` and a nonempty signed cube `σ` at `z`, i.e. signs on some coordinates of one
  flat `F ∋ z`. The **orthant tile** is `O(z, σ)`, the set of `U ∈ ∂` whose first normal cube at `z` is `σ`
  (Niblo–Reeves normal cube paths).
- **Peels.** For `s ∈ σ`, the **peel** `P_s` cuts `O(z, σ)` along the next `s`-hyperplane.
- **Why Thumann applies.**
  - The tiles have finitely many types and trivial stabilizers.
  - Peels in different coordinates commute. The C-split of `V` merges equal colours, which is Thumann's
    colour-tameness.
  - Normal cube paths from any base vertex give "uniform" refinements, and these are reachable from every
    tile.
- **Why earlier attempts stalled.**
  - Li's theorem needs two returns per state (`t < d`), which RAAG codings never have. Thumann needs
    colour-tameness instead, and the Cuntz stabilization supplies it for free.
  - The single-split (normal cube) operad is too small. A translate of a quadrant along one axis is not
    normally reachable, since diagonals from different base points never merge. Coordinate peels repair this.

## Proof

**1. Tiles (any CAT(0) cube complex, then the tree of flats).** For `U ∈ ∂` and a vertex `z`, the set of
hyperplanes adjacent to `z` that separate `z` from `U` is nonempty and pairwise transverse. Two such
hyperplanes, if disjoint, would bound disjoint halfspaces both containing `U`. So they span a cube `σ` at `z`
(links are flag, and there is no inter-osculation). Hence the tiles `O(z, σ)` at a fixed `z` partition `∂`.
Each is clopen, being cut out by the finitely many hyperplanes adjacent to `z`.

In the tree of flats, let `σ` sit in the flat `F ∋ z`. Then `O(z, σ) = π_F^(-1)(R(z, σ))`, where the **box**
`R(z, σ) ⊆ F̄` is a product of one-dimensional intervals `I_c`, one per coordinate `c` of `F`:
- `I_c = (z_c, +∞]` or `[−∞, z_c)` for the coordinates of `σ`, by sign;
- `I_c = {z_c}` for the other coordinates.

Hyperplanes of the other flats through `z` never separate `z` from a `U` with `π_F(U) ≠ z`, since the
incidence graph is a tree. The **vertex cell** of a lattice point `v ∈ F` is
`π_F^(-1)(v) = ⊔ O(v, ρ)`, over the nonempty signed cubes `ρ` of the other flats through `v` (the **hanging
tiles** at `v`). There is at least one other flat, since `k ≥ 2`.

**2. Peels (any CAT(0) cube complex).** Let `s ∈ σ`, let `H_s` be its hyperplane at `z`, and let `zs` be the
vertex across it. Then

  `O(z, σ) = ⊔_τ O(zs, τ)`, over the cubes `τ` at `zs` with `τ ⊇ σ ∖ {s}` whose other hyperplanes are not
  adjacent to `z`.

*Proof.* Take `U ∈ O(z, σ)`.
- The hyperplanes of `σ ∖ {s}` are adjacent to `zs` and separate it from `U`. `H_s` does not separate them.
- Take another hyperplane `k` adjacent to both `z` and `zs`, with `k ∉ σ`. If `k` separated `zs` from `U`, it
  would separate `z` from `U`, which is impossible.

Conversely, let `U` have such a first cube `τ` at `zs`.
- `U` lies across `H_s`, since `H_s` is adjacent to `zs` and not in `τ`.
- Let `k` be adjacent to `z`, with `k ∉ σ`, and suppose `k` separates `z` from `U`.
  - If `k` is transverse to `H_s`, then `k` spans a square with `H_s` at `z`, so `k` is adjacent to `zs` and
    lies in `τ`. That is excluded.
  - If `k` is disjoint from `H_s`, then the two far halfspaces are disjoint. That is impossible, since `U` lies
    in both. `∎`

In the tree of flats this is coordinatewise: the peel `P_s` replaces `I_s = (z_s, ∞]` by the two intervals
`{z_s + 1}` and `(z_s + 1, ∞]`.
- If `{z_s + 1}` makes every interval a point, that piece is the vertex cell of `zs`, which is split into its
  hanging tiles.
- Either way `P_s` has at least two nonempty pieces.

Two consequences:
- **Commutation.** Peels in distinct coordinates act on distinct factors of the box, so `P_s P_(s')` and
  `P_(s') P_s` are the same dissection.
- **Equivariance.** `λ P_s(T) = P_s(λ T)` for `λ ∈ Λ`.

**3. The operad `𝒪`.** Its colours are the finitely many types `σ` (a factor, a nonempty set of its coordinates,
and signs). Put `X_σ = C × O(1, σ)`.
- An operation of colour `σ` is a **reachable dissection** of `X_σ`: a partition produced by finitely many
  C-splits `[u] → [u0] ⊔ [u1]` and peels of tiles.
- Each piece `[u] × O(w, ρ)` is labelled by `X_ρ → [u] × O(w, ρ)`, `(c, U) ↦ (uc, wU)`.

This is a symmetric operad of injective maps. Its only degree-one operations are identities, so `ℐ(𝒪)` is
discrete, which is `F_∞^+`.

**4. Lemma 3 (normal partitions are reachable).** Let `N^D_y` be the partition of `∂` by the first `D + 1` cubes
of the normal cube path from `y`. Its pieces are tiles. Let `S` be a tile and `y` a vertex. Then for all large
`D`, the pieces of `N^D_y` inside `S` partition `S` and form a reachable dissection of `S`.

*Proof.*
- In the tree of flats, a normal cube path from `y` to `U` runs through the flats of the incidence-tree path.
  It enters a flat `F` at its gate `g = g_F(y)` (the vertex of `F` nearest `y`). After `j` steps inside `F` it
  is at `g + clip(π_F(U) − g, j)`, coordinatewise, and it moves on into another flat only at a lattice point.
- So inside `F` the pieces of `N^D_y` are the products of one-dimensional **grid cells** centred at `g`:
  points `{g_c + i}` with `|i| ≤ D'`, and the two rays beyond `g_c ± D'`. The vertex cells are refined further.
- Let `S` have box `B` in `F`, and take `D'` larger than the distance from `g` to every endpoint of `B`. Then
  each interval of `B` is a union of grid cells, and a one-dimensional union of this kind is reached by
  successive peels.
- Peel the first coordinate all the way, then the second on each piece, and so on. This is a product, hence
  guillotine, sequence. It reaches every grid cell of `B`. A cell whose intervals are all points is reached as
  the hanging tiles of its vertex.
- Inside a hanging tile at `v`, in a flat `F'`, repeat the argument with the gate `g_(F')(y)`. This recursion
  follows finitely many flats toward `y` and then is centred at `y`'s own flats. So a single large `D`
  serves. `∎`

**5. Lemma 4 (refinement implies factorization).** Let `Θ` be a reachable dissection of a tile `T` whose
partition refines that of a peel `P_s(T)` (respectively of `C`). Then `Θ = Ψ ∘ P_s(T)` for a reachable `Ψ`.

*Proof,* by induction on the number of pieces of `Θ`. Write `Θ = Θ' ∘ E`, with `E` its first split.
- If `E = P_s`, we are done.
- If `E` is a C-split or a peel `P_(s')` with `s' ≠ s`, let `B` be a piece of `E`.
  - `s` is still a coordinate of `B`'s type. Coordinatewise, the partition `P_s(T) ∧ B` is `P_s(B)`, except that a
    vertex cell of `P_s(B)` is a single cell of `P_s(T) ∧ B`.
  - A reachable piece inside a vertex cell `π_F^(-1)(v)` is a descendant of one hanging tile at `v`. Its last
    ancestor that is a box in `F` was peeled onto `v`.
  - So `Θ'|_B` refines `P_s(B)`, and by induction `Θ'|_B = Ψ_B ∘ P_s(B)`.
  - Commutation (§2) gives `⊗_B P_s(B) ∘ E = ⊗_A E_A ∘ P_s(T)`, with `E_A` the split `E` applied to `A`. So
    `Θ = Ψ ∘ P_s(T)`. `∎`

**6. Thumann's hypotheses.**
- *Finitely many colours.* The number of colours is `Σ_i (3^(n_i) − 1)`.
- *Colour-tame* (Def. `77101`). Two equal colours merge by a C-split, so a reduced object has at most one letter
  of each colour.
- *Cancellative calculus of fractions* (Def. `81202`).
  - Equalization and both cancellations are automatic for operads of injective maps with trivial
    transformations. Equal composites force equal blocks, and every dissection covers its colour.
  - For square filling, take two reachable dissections `θ_1, θ_2` of `X_σ`. Refine both by the uniform
    partition `U_(L,D)`: C-cylinders of length `L`, times the pieces of `N^D_1`.
  - For `L, D` large, each piece of `U_(L,D)` lies in one piece `[u] × W` of `θ_i`, by compactness, since the
    `N^D_1` pieces shrink to points.
  - Through the label `w`, the pieces inside `[u] × O(w, ρ)` are a uniform C-refinement times `w`-translates of
    the `N^D_(w^(-1))` pieces inside `O(1, ρ)`. So they are reachable, by Lemma 3.
- *Finite type* (Defs. `13449`, `24121`, `79040`, `26536`).
  - Transformations are trivial, so classes are operations. By Lemma 4, `Θ_1 ≤ Θ_2` in `𝒯𝒞` for `Θ_1` a C-split,
    a peel, or a composite of these.
  - The very elementary classes of colour `σ` are `C` and `P_s`, `s ∈ σ`. Every dissection factors through its
    first split, and distinct single splits do not refine one another.
  - Let `Θ ≥ P_S` and `Θ ≥ P_(S')`, where `P_S` is the joint peel over `S ⊆ σ`, well defined by commutation.
    Lemma 4, applied on the pieces of `P_S`, gives `Θ ≥ P_(S ∪ S')`, and likewise with `C`.
  - So minimal common upper bounds are unique, and the spine of colour `σ` is `{C^ε P_S : ε ∈ {0,1},
    S ⊆ σ} ∖ {id}`, which is finite.
- *`ℐ(𝒪)` of type `F_∞^+`.* It is discrete (§3).

So `π_1(𝒪, X)` is of type `F_∞` for every object `X` (Theorem `41762`).

**7. `π_1(𝒪, R) = F`, for the root `R = (X_σ)_σ`.** The root is `⊔_σ C × O(1, σ) = C × ∂`.
- *Into `F`.* A fraction `θ' θ^(-1)` is a homeomorphism given on pieces by a prefix replacement times some
  `λ ∈ Λ`, so it lies in `F`.
- *Injective.* If a fraction is the identity, each piece satisfies `(uc, U) ↦ (u'c, w' w^(-1) U) = id`.
  Topological freeness then forces equal labels.
- *Onto (Brin's two-step).* Let `f ∈ F`.
  - Choose a reachable uniform partition `𝒫` of `R` on whose pieces `[u] × T` the map `f` is canonical:
    `(uc, U) ↦ (u'c, λU)`.
  - Let `𝒬_1` be a uniform partition `U_(L,D)` refining `f(𝒫)` as sets. It is reachable. Then `f^(-1)(𝒬_1)`
    consists of pieces `[v'] × λ^(-1) N`.
  - Let `𝒫_2` be a uniform partition refining `f^(-1)(𝒬_1)`. It is reachable.
  - Inside each `f^(-1)(Q)`, with `Q = [v] × N`, the pieces of `𝒫_2` are a relative C-refinement times the
    `N^(D_2)_1` pieces inside `λ^(-1) N`. `f` carries them to a C-refinement times the `N^(D_2)_λ` pieces inside
    `N`. By equivariance and Lemma 3 (base `λ`), these form a reachable dissection of `Q`.
  - So `f(𝒫_2)` is reachable, and `f = f(𝒫_2) ∘ 𝒫_2^(-1)` as a fraction.

This proves item 1. Item 2 then follows from `special-cube-complex-groups-lie-in-fp-members-of-class-c`,
whose only open gate was E3′. `∎`

## Beyond disjoint unions of cliques: the induction on the defining graph

Only three inputs were used: the tile partition (§1), coordinatewise peels (§2), and Lemmas 3 and 4. What makes
them work is that **vertex spaces are products** and they are **glued along a tree**.

- **Disjoint union** (`A_(Γ_1 ⊔ Γ_2) = A_1 * A_2`). The complex is a tree of copies of `X̃_1` and `X̃_2`, glued at
  vertices. §1–§7 run verbatim with the boxes replaced by the tiles of the factor, and the vertex cells split
  into the other factor's tiles.
- **Join** (`A_(Γ_1 * Γ_2) = A_1 × A_2`). Cubes are `σ_1 ⊔ σ_2`, and a tile is a product of factor regions in
  `X̄_1 × X̄_2`, where a factor with `σ_i = ∅` contributes the point `z_i`. Peels act factorwise, so Lemmas 3 and 4
  hold if they hold in each factor's Roller *compactification*, including principal points.

**Corollary (sketch, not proved here).** E3′ holds for `A_(Γ⊔{v})` for every **cograph** `Γ` (a `P_4`-free graph,
built from points by disjoint unions and joins). This needs the join step written out in the compactification
version.

**Frontier.** The first graph that is not a cograph is the path `P_4 = a − b − c − d`. There the peel lemma and
commutation (§2) still hold, since they were proved for every CAT(0) cube complex. What must be checked is
Lemma 4's hypothesis `P_s(T) ∧ B = P_s(B)`, and the guillotine step of Lemma 3. These are local statements about
normal cube paths in `X̃_(P_4)`.

## Lesson for general BH

**The V factor pays for loop-richness, and product-like vertex spaces pay for the calculus of fractions.**
- Li's finiteness theorem needs every state to return twice (`t < d`), which RAAG cube codings never satisfy.
- Thumann's theorem needs colour-tameness instead. The Cuntz stabilization gives colour-tameness for free, since
  two equal colours merge by a C-split.
- What remains is geometric:
  - one split per tile is too few, because diagonal normal paths from different base points never merge;
  - one split per *coordinate* is right, because peels commute (cube property).

So E3′ for Roller hosts reduces to local confluence of coordinate peels (Lemmas 3 and 4). This holds on trees of
products, which covers every cograph by induction on the defining graph. The first real test is `P_4`.

## Credit

- Normal cube paths are due to Niblo–Reeves.
- The finiteness theorem is Thumann's.
- The tree template is `cocompact-tree-end-shift-hosts-are-f-infinity` (bh-invent-17).
- The route, and the E3′ gate, are due to bh-ref-hl.
- Greedy (normal) cube codings for RSGs are the related work of `greedy-cube-codings-make-cubulated-hyperbolic-groups-rsgs`.

## Referee (bh-ref-hl, 2026-09-19): PASS for items 1 and 2

This is an internal lane review, line by line. I re-read Thumann's Theorem `41762` and Definitions `81202`, `79040`, `13449`,
`24121`, `26536` and `77101` in the LaTeX source on MSI (`gqsrc/bh-invent-07/thumann.tex`). The hypotheses are exactly: finitely many
colours, colour-tame, cancellative calculus of fractions, finite type, and `ℐ(𝒪)` of type `F_∞^+`.
- **§1 (tiles).**
  - Nonemptiness holds because a hyperplane separating `z` from `U`, with no hyperplane between, is adjacent to `z`.
  - Pairwise transversality comes from the 1-ball rule of `roller-compactifications-of-cube-complexes-are-sfts`: disjoint
    hyperplanes adjacent to `z` have disjoint far halfspaces. Transverse hyperplanes adjacent to `z` span a square at `z` in a
    CAT(0) cube complex.
  - In the tree of flats, `O(z,σ) = π_F^(−1)(R(z,σ))`. Hyperplanes of other flats at `z` have far halfspaces disjoint from those of
    `F`, again by the 1-ball rule.
  - Correct.
- **§2 (peels).**
  - Both inclusions check, including the transverse and disjoint cases for `k ∉ σ`.
  - Coordinatewise, the pieces at `zs` are `{z_s+1}` and `(z_s+1, ∞]`. Other coordinates of `F` stay points, because their
    hyperplanes are adjacent to both `z` and `zs`.
  - Commutation holds, including the vertex-cell case, which both orders split into hanging tiles.
  - Correct.
- **§3–§4 (operad, Lemma 3).**
  - Pieces are always `[u] × O(w,ρ)`, and composition gives `[uu′] × O(ww′,ρ′)`. Degree-one operations are identities.
  - In the tree of flats a normal cube path moves diagonally in each flat (`g + clip(·, j)`). So the pieces are grid cells centred
    at the gate, and every interval of a box is reached by one-directional peels once `D′` exceeds the distance from the gate to the
    corners.
  - **Precision.** Suppose `U ∈ S` returns toward `y` through the gate, i.e. `π_F(U) = g`. Then the recursion continues in the flat
    `F′ ∋ g` toward `y`, centred at `g_(F′)(y)`. This is covered by "repeat with the gate" but deserves a sentence.
  - Correct.
- **§5 (Lemma 4).**
  - The only non-coordinatewise point is the vertex cell. A reachable piece inside `π_F^(−1)(v)` has a last box-ancestor in `F`, and
    that ancestor was peeled onto `v`. So the piece lies in one hanging tile.
  - Commutation then rearranges `⊗_B P_s(B) ∘ E` into `⊗_A E_A ∘ P_s(T)`. Correct.
- **§6 (Thumann's hypotheses).**
  - *Colour-tame.* A C-split merges two equal colours, so a reduced object has at most one letter per colour.
  - *Cancellativity and equalization.* Dissections cover their colour, and labels are injective, so equal composites force equal
    blocks.
  - *Square filling.* Refine both sides by the uniform `U_(L,D)`. Pull it back through the labels by equivariance, and apply Lemma 3
    with base `w^(−1)`. The labels agree because a piece determines its cylinder and its tile apex.
  - *Finite type.* The very elementary classes are `C` and the `P_s`. Lemma 4 gives unique minimal common upper bounds `P_(S∪S′)` and
    `C·P_S`, with the vertex-cell case handled as in Lemma 4. So the spine (Construction `45209`) is `{C^ε P_S} ∖ {id}`, which is
    finite.
  - *`ℐ(𝒪)`.* It is trivial, hence `F_∞^+`.
- **§7 (`π_1 = F`).** Brin's two-step works: `f` is locally a prefix replacement times some `λ`, the uniform partitions are reachable,
  and `f` carries the `N^D_1` pieces to `N^D_λ` pieces, which is Lemma 3 with base `λ`. Correct.
- **Item 2.** It uses the Remark of `special-cube-complex-groups-lie-in-fp-members-of-class-c` (`X ≅ ∂_R`). That Remark now carries a
  complete proof, by the valley argument along tree paths. Its author is bh-ref-hl, so that proof is still single-lane. With it,
  E3′ holds for `A_(Γ⊔{v})` for every clique union `Γ`, and the route runs end to end. As the node says, this is calibration.
- **Not refereed.** The cograph corollary and the `P_4` frontier, which are correctly labelled as a sketch.
- **Housekeeping.** The claim frontmatter carries `requires:` in the old schema. A `-proof` route would match the current graph
  convention.
