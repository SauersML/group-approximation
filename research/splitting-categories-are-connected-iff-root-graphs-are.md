---
rg: 2
id: splitting-categories-are-connected-iff-root-graphs-are
kind: claim
title: In a dissection operad the splitting category of a dissection with at least three pieces is connected exactly when its root graph is connected, so only minimal common upper bounds of two atoms split disconnectedly and condition (G) for finite presentation is a statement about pairs of atoms
requires:
  - thumann-finiteness-without-finite-type
  - edge-split-flop-spine-elements-split-disconnectedly
distinct_from:
  thumann-finiteness-without-finite-type: that proves finite presentation from condition (G), connected splitting categories of large elementary classes; this decides when a splitting category is connected and reduces (G) to minimal common upper bounds of pairs of atoms.
  edge-split-flop-spine-elements-split-disconnectedly: that computes the splitting category of the two flop elements of the edge-split operad by hand; this explains the answer (two atoms, no third one) and shows that no element above the first spine level splits disconnectedly.
  stein-complex-elementary-intervals-are-grid-spheres: that computes the full homotopy type for twisted Brin–Thompson grids; this gives connectivity only, for every dissection operad.
---

**ESTABLISHED** (lane bh-invent-07, 2026-09-18). This is an elementary lane proof; one referee PASS (bh-ref-engines, 2026-09-18), with the hypothesis corrected to non-atoms; see Referee section. No priority is claimed.

## Setting

- **The operad.** `𝒪` is a dissection operad as in `non-lcm-dissection-operad-groups-are-f-infinity`:
  finitely many tiles, transformation groups that are finite, and generating subdivisions.
  Its classes are dissections.
- **Dissections and the order.** For a tile `P`, `𝔇(P)` is the set of dissections of `P`.
  `D ≤ D'` means `D'|_p ∈ 𝔇(p)` for every piece `p` of `D`.
- **Atoms.** The *atoms* are the very elementary classes, the minimal nontrivial dissections.
- **Split trees.**
  - A *split tree* of `D` is a rooted tree of tiles in which each internal node is subdivided
    by an atom of that node, and whose leaves are the pieces of `D`.
  - Every dissection has one (Thumann, arXiv:1409.1085, remark after Def. `13449`).
  - For an atom `ρ` of the root tile, `ρ ≤ D` exactly when `ρ` is the root of some split tree
    of `D`.
- **Cherries.** A *cherry* of a split tree is an internal node all of whose children are
  leaves. For a cherry `Q`, `D_Q` is `D` with the children of `Q` merged back into `Q`.
- **First spine level.** `M(ρ, ρ')` is the set of minimal common upper bounds of distinct
  atoms `ρ, ρ'`. `S_1 = ⋃ M(ρ, ρ')` is the first level of the spine (Construction `45209`),
  so every element of `S_1` is elementary.
- **Splitting category.** `𝒜(Θ)` is as in `thumann-finiteness-without-finite-type`: the
  dissections `D` with `triv < D < Θ` such that `Θ|_p` is elementary or trivial on every piece
  `p` of `D`. It is defined here for every `Θ` with at least three pieces, not only for spine
  elements.
- **Root graph.** `R(Θ)` has as vertices the atoms `ρ ≤ Θ` of the root tile. It has an edge
  `ρ — ρ'` exactly when `Θ ∉ M(ρ, ρ')`, that is, when `ρ` and `ρ'` have a common upper bound
  strictly below `Θ`.

## Statement

**Theorem.** Let `Θ` be a dissection with at least three pieces. Then `𝒜(Θ)` is connected if
and only if `R(Θ)` is connected.

**Corollary 1 (two sides only at level one).** If `Θ ∉ S_1`, then `R(Θ)` is complete, so
`𝒜(Θ)` is connected. A disconnected splitting category can occur only for a minimal common
upper bound of two atoms.

**Corollary 2 (condition (G) is about atom pairs).** Condition `(G)_2` of
`thumann-finiteness-without-finite-type` is the condition for finite presentation. It holds
if and only if every element of `S_1` of large degree has a connected root graph. It holds in
particular when each pair of atoms has minimal common upper bounds of bounded degree. For a
finitely generated operad that means finitely many.

**Corollary 3 (sharpness for the Morse method).** Let `Θ` be strictly elementary with `𝒜(Θ)`
disconnected, with `c ≥ 2` components. Let `𝒦` be the object formed by its pieces. Then
`π_1(lk↓(𝒦))` has a free factor of rank `c − 1`, as soon as `Core(𝒦)` is connected.
- So if such `Θ` occur in unbounded degree, Thumann's Morse argument cannot prove finite
  presentation.
- The group may still be finitely presented; this is only a limit on the method.

## Proof

**Lemma 1 (cherries dominate).** Every `D ∈ 𝒜(Θ)` satisfies `D ≤ D_Q ∈ 𝒜(Θ)` for some cherry
`Q` of some split tree of `Θ`.
- Since `D < Θ`, a split tree of `D` extended by split trees of the restrictions `Θ|_p` is a
  split tree `τ` of `Θ`.
- Some `Θ|_p` is nontrivial. Its subtree contains a cherry `Q` of `τ`, and `τ` minus `Q` shows
  `D ≤ D_Q`.
- `D_Q ∈ 𝒜(Θ)`: `Θ|_{D_Q}` is one atom on `Q`, and `D_Q` is nontrivial because `Θ` has at
  least three pieces. `∎`

**Lemma 2 (one tree, one component).** The `D_Q`, for `Q` a cherry of one split tree `τ`, lie
in one component.
- Take two cherries `Q ≠ Q'`. They are disjoint, and `τ` minus both gives `D_{QQ'}`.
- `D_{QQ'}` lies below `D_Q` and `D_{Q'}` and restricts to two atoms. It is nontrivial, since a
  tree with two cherries has at least four leaves. `∎`

**Moves.** A *move* at a node `N` changes a split tree only inside `N`. There it replaces a
split tree of some `p ∈ M_N(ρ, ρ')` by another split tree of the same `p`, keeping the
subtrees below the pieces of `p`. A move is *at the top* if `N` is the root tile.

**Lemma 3 (coherence).** Let `E ∈ 𝔇(P)`. Any two split trees `σ, σ'` of `E` are joined by a
sequence of moves. The moves at the top can be chosen to use `p ∈ M(ρ, ρ')` with `p ≤ E`,
where `ρ, ρ'` are the roots of two consecutive trees.

Induction on the number of pieces:
- **Same root `ρ`.** The subtrees at the pieces of `ρ` are split trees of smaller
  dissections. By induction they are joined by moves, which happen inside those pieces, so
  never at the top. Change them one piece at a time.
- **Different roots `ρ ≠ ρ'`.**
  - `E` is a common upper bound of `ρ` and `ρ'`, so some `p ∈ M(ρ, ρ')` has `p ≤ E` (Thumann,
    Obs. `61724`).
  - `p` has split trees `π` with root `ρ` and `π'` with root `ρ'`. Extending both by one choice
    of split trees of the `E|_q`, for the pieces `q` of `p`, gives trees `σ_1, σ_1'` of `E`.
    They differ by one move at the top with this `p`.
  - Join `σ` to `σ_1` and `σ_1'` to `σ'` by the same-root case. `∎`

**Lemma 4 (good moves).** Suppose `τ, τ'` differ by a move at `N` with `p`, and
`(N, p) ≠ (root, Θ)`. Then the `D_Q` of `τ` and of `τ'` lie in one component of `𝒜(Θ)`.
- **Some piece of `p` has a nontrivial subtree.** That subtree is the same in both trees and
  contains a cherry common to `τ` and `τ'`.
- **Otherwise `Θ|_N = p`, and `N` is not the root.**
  - Let `D` be `Θ` with `N` merged. It is a dissection, nontrivial, and `Θ|_D = p` on `N`, which
    is elementary. So `D ∈ 𝒜(Θ)`.
  - `τ` has a cherry `Q` inside `N`, and `D ≤ D_Q`. Likewise `τ'` has a cherry `Q'` inside `N`
    with `D ≤ D_{Q'}`. `∎`

**Proof of `⇐`.**
- Let `σ, σ'` be split trees of `Θ`, with roots `ρ, ρ'`. Choose a path
  `ρ = ρ_0 — ρ_1 — ⋯ — ρ_k = ρ'` in `R(Θ)`.
- Each edge gives `p_i ∈ M(ρ_i, ρ_{i+1})` with `p_i ≤ Θ` and `p_i ≠ Θ`, since `Θ` is not
  minimal for that pair. Through `p_i`, trees with roots `ρ_i` and `ρ_{i+1}` differ by one top
  move that is good.
- Between these trees, use the same-root case of Lemma 3. Its moves are not at the top, so
  they are good.
- By Lemmas 2 and 4, the cherries of all split trees lie in one component. By Lemma 1, every
  element of `𝒜(Θ)` is comparable to one of them. So `𝒜(Θ)` is connected.

**Proof of `⇒`.**
- Suppose `R(Θ)` splits into nonempty parts `A_1, A_2` with no edge between them. For each
  `i`, let `U_i` be the elements of `𝒜(Θ)` lying above some atom in `A_i`.
- Every `D ∈ 𝒜(Θ)` lies above the root atom of one of its split trees, and that atom is in
  `A_1` or `A_2`. So `U_1 ∪ U_2 = 𝒜(Θ)`.
- The `U_i` are disjoint. An element above both `a_1 ∈ A_1` and `a_2 ∈ A_2` would be a common
  upper bound strictly below `Θ ∈ M(a_1, a_2)`.
- Each `U_i` is an up-set, so there are no order relations between them.
- Each `U_i` is nonempty: `U_i ∋ D_Q` for a cherry `Q` of a tree with root in `A_i`, because
  `Θ` has at least three pieces. So `𝒜(Θ)` is disconnected. `∎`

**Proof of Corollary 3.**
- In `Corona(𝒦)` the object `v = (one piece, θ)` has link exactly `𝒜(Θ)`. Nothing lies above
  it, and the elementary arrows below it are the elements of `𝒜(Θ)`.
- It is last in the Morse order, and the rest is connected because every earlier descending
  link is nonempty. So `Corona(𝒦) = R ∪ cone(𝒜(Θ))` with `R` connected.
- Van Kampen gives the free factor. `lk↓(𝒦) ≃ Corona(𝒦)` by the spine argument (Thumann,
  Prop. `29625`). `∎`

## Calibration

- **Brin–Thompson and twisted Brin–Thompson groups.**
  - The atoms are the single splits `θ_s`, and `M(θ_s, θ_t) = {θ_{st}}`.
  - `R(θ_{st})` is two vertices with no edge, and `𝒜 ≃ S^0` is disconnected.
  - For `|C| ≥ 3`, the full split `θ_C` is not in `S_1`, so `𝒜(θ_C)` is connected. This agrees
    with `≃ S^{|C|−2}` (`stein-complex-elementary-intervals-are-grid-spheres`).
- **Edge-split flops.**
  - `F_± ∈ M(E_01, E_02)`, and the only atoms below them are `E_01` and `E_02`
    (`edge-split-flop-spine-elements-split-disconnectedly`).
  - So `R(F_±)` has no edge, and `𝒜(F_±)` is disconnected. This agrees with that node's
    direct computation `≃ S^0`.

## Consequence for the closed-MCG host

- By `thumann-finiteness-without-finite-type` and Corollary 2, the edge-split group `G_E` is
  finitely presented if:
  - Ore's condition holds (`edge-split-operad-has-common-refinements`); and
  - **(R_E)** every minimal common upper bound of two edge splits, of large degree, has a
    connected root graph.
- (R_E) holds in particular under **(B_E)**: pairs of edge splits have only finitely many
  minimal common upper bounds.
- This is rank-free and replaces the finite spine of `edge-split-operad-satisfies-ore`.
  **Nothing above the first spine level needs to be checked.**
- By `S_{m+1}`-symmetry there are two pair types: adjacent edges, with the flops `F_±`, and
  disjoint edges, with the square of commuting splits.
- (B_E) says there are no exotic minimal common upper bounds of large degree. An exotic one
  would be a common upper bound of `E_a` and `E_b` that dominates none of these.
  - Geometry does not exclude them, since `≥_E` is not geometric refinement
    (`edge-split-order-is-not-geometric-refinement`).
  - An exotic one is harmless if a third atom links its two sides in its root graph.
- **Finite test.**
  - Rank 2: search the common upper bounds of `E_01` and `E_02` that are `≥_E` neither `F_+`
    nor `F_−`.
  - Rank 3: do the same for disjoint edges against the square.
  - For each minimal one found, check whether `E_12` (or another atom) lies below it with
    smaller common upper bounds for both new pairs.
  - If none exist up to a bound that also closes the argument, (B_E) holds.
- **Update (search, 2026-09-18).** Exotic two-sided bounds do exist.
  - In rank 4 the commuting pair `E_01, E_23` has a 13-piece minimal common upper bound that
    is not above the square, with root graph `{E_01, E_23}` and no edge
    (`disjoint-edge-splits-have-an-exotic-two-sided-minimal-bound`).
  - So (B_E) in the form "only squares and flops" is false.
  - (R_E) now asks for bounded degree of these pinwheel-type elements in each rank.
  - In rank 3 nothing exotic was found in the searched range.

## Lesson for general BH

**Split trees of one dissection are coherent.** Any two are joined by local moves at minimal
common upper bounds of two atoms. Such a move separates the splitting category only when it is
the whole dissection. So every splitting category is connected except at the first spine
level, exactly as full splits in two directions are the only disconnected ones in
Brin–Thompson groups.

For Thompson-like hosts built from local moves (the closed-MCG and Deligne dissection hosts),
the finiteness gate therefore changes. It is no longer "is the spine finite?" but "do pairs of
atoms have finitely many two-sided minimal common upper bounds?". That is a question about two
moves at a time.

## Referee (bh-ref-engines, 2026-09-18): PASS, with one hypothesis corrected

I checked Lemmas 1–4, both directions of the Theorem, and Corollaries 1–3.
- *Lemma 1.* A split tree of `D`, extended by trees of the `Θ|_p`, has a cherry `Q` strictly below the root,
  since `D` is nontrivial. So `D ≤ D_Q ∈ 𝒜(Θ)`.
- *Lemma 3 (coherence).* Minimal common upper bounds exist below any common upper bound, because a dissection
  has only finitely many coarsenings. Same-root moves stay off the top.
- *Lemma 4.* Correct in both cases.
- *`⇐`.* Correct.
- *`⇒`.* The `U_i` are disjoint up-sets covering `𝒜(Θ)`. Disjointness is exactly the missing root-graph
  edge.
- *Corollaries.* Corollary 3's free factor follows from van Kampen for a cone on a `c`-component link
  attached to a connected complex. It is correctly stated as a limit on the Morse method only.

**Hypothesis fix.** "At least three pieces" should read "**not an atom**". An atom of degree `≥ 3`, for
example a tree split with three children, has `𝒜(Θ) = ∅` (disconnected) but a one-vertex, connected root
graph. Every non-atom has at least three pieces. The nonemptiness steps in Lemma 1 and in `⇒` use exactly
non-atomicity. All applications concern strictly elementary classes, which are never atoms, so no corollary
changes.

**The index correction to `thumann-finiteness-without-finite-type`** made in 5a7d8353eb is checked there.

**Credit.** Thumann (arXiv:1409.1085) for the spine, the corona and Obs. `61724`. The Brin–Thompson calibration
(full splits in two colours give `S^0`) matches the grid-sphere computation.
