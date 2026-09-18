---
rg: 2
id: decidable-free-subshifts-pass-to-graphs-of-groups
kind: claim
title: If a group splits as a finite graph of groups whose vertex groups carry free subshifts with decidable language, and its word and vertex/edge membership problems are decidable, then it carries a free subshift with decidable language; trees, infinite emitters included, cost nothing
distinct_from:
  decidable-groups-carry-free-subshifts-with-decidable-language: that is premise (D) for every infinite fp decidable group, open; this proves (D) is preserved by amalgams and HNN extensions with decidable data, so (D) holds for every group with such a hierarchy down to (D)-groups, and for (FA) inputs it localizes to the vertex group that contains them.
  free-products-with-z-inherit-m2-from-decidable-free-subshifts: that turns (D) for A into (M2) for A * Z, using the tree of A * Z to glue and minimize; this uses a tree only to kill hyperbolic elements, keeps (D), and allows arbitrary vertex and edge groups.
  effectively-rf-groups-have-effective-minimal-free-subshifts: that gives (M2), hence (D), from finite quotients; the instances here include groups with no finite quotients at all (Burger-Mozes simple groups) and non-residually-finite Baumslag-Solitar groups.
---

**ESTABLISHED** (lane proof, bh-invent-14, 2026-09-18; elementary; not reviewed). No priority is
claimed. The tree layer below is a Busemann function read through an aperiodic word.

## Setting

- `G` is the fundamental group of a finite graph of groups, with Bass–Serre tree `T`. `G` acts on
  `T` without inversions. Vertices of `T` are the left cosets `hG_v` (one base vertex `v` per vertex
  orbit), and edges are the left cosets `hG_e`.
- Every vertex group `G_v` is finitely generated. Edge groups are arbitrary.
- **(H1)** `G` is finitely generated with solvable word problem.
- **(H2)** Membership in every vertex group `G_v` and every edge group `G_e` is decidable in `G`.
  So normal forms, cosets and geodesics of `T` are computable.
- **(H3)** Every `G_v` has **(D)**: a nonempty subshift `Y_v ⊆ C_v^{G_v}` on which `G_v` acts freely,
  with decidable language. Finite vertex groups have (D) trivially.
- Shifts act on the left: `(g·x)(h) = x(g^{-1}h)`.

## Theorem

Under (H1)–(H3), `G` has (D): there is a nonempty free subshift `Y ⊆ Σ^G` with decidable language.

**Corollaries** (hypotheses checked by the normal form theorems):
1. **Free groups and free products.** Free products of finitely many (D)-groups with decidable word
   problem have (D). The edge groups are trivial.
2. **Generalized Baumslag–Solitar groups.** Every GBS group has (D), including the
   non-residually-finite `BS(m,n)` with `2 <= |m| != |n|`. Their vertex and edge groups are `Z`,
   and membership is decided by Britton's lemma.
3. **Burger–Mozes groups.** Every amalgam `F *_{F'} F''` of finitely generated free groups over
   finite-index subgroups has (D). This includes the Burger–Mozes finitely presented simple groups.
   They have no finite quotients, so no Toeplitz or residual-finiteness argument reaches them.
4. **Hierarchies.** (D) holds for every group with a finite hierarchy of such splittings whose
   terminal vertex groups have (D). By `free-products-with-z-inherit-m2-from-decidable-free-subshifts`,
   each such `G` makes `G * Z` satisfy (M2).

## Proof

`Y` is a product of three kinds of independent layers.

**1. Vertex layers.** For each base vertex `v`, take a layer `ℓ_v : G → C_v` with the condition
`(V_v)`: for every `h ∈ G`, the configuration `y_h(a) = ℓ_v(ha)` on `G_v` lies in `Y_v`.
- *Well defined.* Replacing `h` by `ha_0` (`a_0 ∈ G_v`) replaces `y_h` by the shift `a_0^{-1}·y_h`,
  which lies in `Y_v` too.
- *Invariant and closed.* The condition for `g·x` at `h` is the condition for `x` at `g^{-1}h`.
  Each `y_h ∈ Y_v` is a closed condition.
- *Nonempty.* Choose one point of `Y_v` per coset, independently.

**2. Orientation layer.** For each base edge `e`, a symbol `o_e(h) ∈ {→, ←}` records the direction
of the edge `hG_e`. It is required to be constant on cosets of `G_e`, which is effectively closed:
enumerate `G_e` by (H2). The one further condition is:

`(O)` no vertex of `T` has two outgoing edges.

Configurations satisfying (O) are exactly the *end orientations* (every edge points toward a fixed
end `ξ`) and the *root orientations* (every edge points toward a fixed vertex `w`).
- **At most one sink.** On the path between two sinks the direction changes somewhere, and there
  a vertex has two outgoing edges.
- **No sink.** If no vertex is a sink, the parent edges form rays that all merge, and they converge
  to one end.

Each orientation has a height `β : V(T) → Z`, unique up to an additive constant, with
`β(child) = β(parent) + 1`.

**3. Height-colour layer.** Fix the Thue–Morse subshift `S ⊆ {0,1}^Z`. It is minimal and infinite,
so every point is aperiodic, and its language is decidable. A colour `κ_v(h) ∈ {0,1}` is attached
to the vertex `hG_v`, constant on cosets of `G_v`. The condition is:

`(K)` `κ = σ ∘ β` for some `σ ∈ S`.

On every finite set of vertices, (K) says two things: equal relative heights carry equal colours,
and the colour word along the heights is in `L(S)`. By compactness of `S`, the finite conditions
imply (K). Limits of configurations satisfying (O) and (K) satisfy them too, because relative
heights stabilize on finite sets. So layers 2 and 3 together form a subshift `Z_T`.

**Freeness.** Suppose `g·x = x` for `x ∈ Y`.
- *`g` elliptic.* Then `g` fixes a vertex `hG_v`, so `g = h a_0^{-1} h^{-1}` with `a_0 ∈ G_v`.
  From `ℓ_v(g^{-1}ha) = ℓ_v(ha)` we get `y_h(a_0 a) = y_h(a)` for all `a`. So `a_0^{-1}` fixes
  `y_h ∈ Y_v`, which forces `a_0 = 1` by freeness of `Y_v`. Hence `g = 1`.
- *`g` hyperbolic, with translation length `τ ≥ 1` and axis `A_g`.*
  - `g` preserves the orientation, so it fixes its target. A hyperbolic automorphism fixes no
    vertex, so the orientation is an end orientation toward some `ξ` with `gξ = ξ`. Then `ξ` is an
    end of `A_g`.
  - `β ∘ g − β` is constant, since `g` maps parent edges to parent edges. On `A_g` it equals
    `±τ ≠ 0`.
  - Invariance of `κ` gives `σ(n ± τ) = σ(n)` for every height `n` of a vertex. The heights along
    `A_g` are all of `Z`. So `σ` is periodic, a contradiction.

  Every nontrivial `g` is elliptic or hyperbolic, because there are no inversions. So `G` acts
  freely on `Y`.

**Decidable language.** The layers are independent, so a finite pattern extends iff each of its
layer patterns does.
- *Vertex layers.* Split the pattern's domain `F` into cosets `hG_v`, using (H2). Transport each
  piece to a pattern on a finite subset of `G_v`: search for `G_v`-words, which terminates by (H1)
  and (H2). The piece extends iff it lies in `L(Y_v)`. Pieces on different cosets are
  unconstrained against each other, so the pattern extends iff every piece does.
- *Tree layers.*
  - Compute the finite convex hull `T_F` of the named edges and vertices, from geodesics given by
    normal forms.
  - The target of an orientation is either (a) a vertex `w ∈ T_F` as a sink, or (b) something
    outside `T_F`, reached from some `w ∈ T_F` through an edge not in `T_F`. If `T` is locally
    finite, check that such an edge exists. At an infinite emitter it always does.
  - For each of these finitely many cases, the orientation on `T_F` and the relative heights of
    the named vertices are determined. Check the named edge directions.
  - Then check that equal relative heights carry equal colours, and that some completion of the
    height word over its gaps lies in `L(S)`.
  - Any case that passes extends: pick an actual target, which fixes `β` on all of `T`, and a
    `σ ∈ S` containing the word at the right offset.

`Y` is nonempty, since `T` has an end or a vertex and every `Y_v` is nonempty. ∎

**Checks.**
- *Free groups.* With trivial vertex groups, the tree layer alone gives (D), as it must: every
  nontrivial element is hyperbolic.
- *Trivial splitting.* `T` is a point, only root orientations exist, and `Y` is `Y_v` again.
- *No hypothesis on the edge groups* beyond decidable membership. They may be infinitely
  generated, and the vertex valence may be infinite.

## Where the input sits: (FA) localization

**Lemma.** If `K ≤ G` has Serre's property (FA), then in every finite hierarchy of splittings of
`G`, `K` is conjugate into a terminal vertex group.

*Proof.* At each level `K` fixes a vertex of the Bass–Serre tree (Serre), so `K` lies in a
conjugate of a vertex group. Induct down the hierarchy. ∎

**Consequence for E1.**
- The master route needs (D) only for some finitely presented decidable envelope `Λ_1 ⊇ K × F_2`
  (`minimal-free-sft-via-decidable-free-subshift-of-the-envelope`).
- By the theorem, (D) for `Λ_1` follows from (D) for the terminal vertex groups of any decidable
  hierarchy of `Λ_1`.
- By the lemma, when `K` is a simple Kazhdan input (Kazhdan implies (FA)), one terminal vertex
  group contains `K`. Trees therefore cannot manufacture (D) for the input. They only move the gate
  down to the vertex group that holds `K`.
- **Conditional reduction.** Suppose `Λ_1` can be built from `K × F_2`, free groups and finite
  groups by finitely many free products, amalgams and HNN extensions with decidable membership.
  Then (D) for `K` alone implies (D) for `Λ_1`, since products preserve (D) and `F_2` has it.
  The effectivity core of E1 is then a property of the input group.

  Whether Clapham's decidable Higman embedding
  (`clapham-fp-embedding-preserves-word-problem`) can be arranged as such a tower is not checked
  here. It is the natural next step.

## Lesson for general BH

**Trees are transparent to effectivity.**
- A Busemann function read through one aperiodic word kills every hyperbolic element of any tree
  action, and its extension problem is a finite case check on the convex hull. This works at
  infinite emitters too.
- So the E1 premise (D), the effectivity core of existence, is *emitter-blind*. Infinite emitters
  obstruct only finite type (E2 and finite presentation), never existence or decidability of
  languages.
- Complexity is paid exactly where the carrier principle says: by the acting group's word and
  membership problems (the decider computes the tree geometry and nothing else) and by the
  elliptic vertex groups.
- For (FA) inputs, which include every Kazhdan simple input, (D) localizes to the vertex group
  containing the input.
- **What remains of E1's effectivity gate** is (D) for (FA) groups: a free subshift with decidable
  language on a group that acts on no tree. That is where a new idea must enter, for instance a
  flexible constraint system with computable look-ahead.
