---
rg: 2
id: symmetric-ore-operads-containing-their-carrier-are-full-groups
kind: claim
title: A symmetric refinement operad with the calculus of fractions whose pieces are identified by local maps of a group Λ is exactly the full group of Λ as soon as its operad group contains Λ; saturation is automatic from Ore, so every refinement host of a carrier is the canonical full group and finiteness is its only gate
distinct_from:
  ore-operad-groups-contain-the-derived-full-group: that obtains only the derived subgroup of the full group, through Matui's simplicity theorem, and needs minimality and pure infiniteness; this obtains the whole full group from Ore and symmetry alone, with no dynamical hypothesis and no recalled theorem.
  edge-split-ore-iff-synchronization-and-tree-domination: that proves saturation for the edge-split operad from (Sync_m) and (TD) by explicit domination; this proves saturation in every symmetric Ore operad containing its carrier, and recovers that case, since (Sync_m) is established there and (Ore) is then equivalent to (TD).
  fp-symmetric-operad-groups-lie-in-the-permutational-class: that proves an operad group is full for its own local maps; this identifies those local maps with the local maps of a prescribed carrier group, so the operad group is a named full group.
  bounded-refinement-operads-reduce-to-their-carriers: that is the transformation channel, where bounded refinement makes the carrier an actor on its moves; this is the dynamics channel, where the carrier acts by fractions and its pair orbits on tiles never enter.
---

**ESTABLISHED** (lane bh-typeA-universal, 2026-09-18). The proof is short and given below; it
applies Step 2 of `symmetric-operad-groups-full-cantor-proof`. Not independently reviewed. No
priority claimed.

## Setting

- `Y` is a Cantor space and `Λ ≤ Homeo(Y)` is any group, the **carrier**.
- `[[Λ]]` is the group of homeomorphisms of `Y` that agree, on each piece of some finite clopen
  partition, with an element of `Λ`. For an effective ample groupoid `𝒢`, read `𝒢`-local maps,
  and let `Λ` be any germ-generating group of `𝒢`-local maps.
- `𝒪` is a **symmetric refinement operad on `Y` with `Λ`-local identifications**. This is the
  setting of `non-lcm-dissection-operad-groups-are-f-infinity`, with only the following assumed.
  - Each color `c` has a model tile `Y_c`, a compact open set.
  - An operation of arity `k` with output `c` is a partition of `Y_c` into `k` clopen pieces, each
    identified with a model tile by a `Λ`-local homeomorphism.
  - Transformations are `Λ`-local self-homeomorphisms of model tiles, and they form groups
    `ℐ_c`.
  - Composition is substitution. Fractions may match pieces by arbitrary color-preserving
    bijections; this is the symmetric case.
- The object `X` is a tuple of colors whose tiles are identified `Λ`-locally with a clopen
  partition of `Y`. `G_𝒪 = π_1(𝒪, X)` acts on `Y` by fractions `e∘d^{-1}`: the `d`-pieces are
  mapped onto the `e`-pieces through the model tiles.
- **Hypotheses.**
  - **(Ore)** the cancellative calculus of fractions;
  - **(B)** the pieces of expansions of `X` form a basis of `Y`;
  - **(C)** `Λ ≤ G_𝒪`, that is, every element of `Λ` is a fraction. For the conclusion it is
    enough that some `Λ_0 ≤ G_𝒪` has the same local maps as `Λ`.

## Statement

1. **Saturation.** `G_𝒪 = [[Λ]]`.
2. **The host is canonical.** Any two operads satisfying the hypotheses for the same carrier
   `Λ ↷ Y` have the same group, `[[Λ]]`. The operad serves only as a certificate of finiteness
   for `[[Λ]]`.
3. **The dynamics-channel reduction of PBH.** Assume in addition:
   - `𝒪` is finitely generated, with finitely many colors, color-tame and with finite groups
     `ℐ_c`;
   - its color monoid has a single nonzero class (see `fp-symmetric-operad-groups-lie-in-the-permutational-class`);
   - (G)_2 holds: the splitting categories of the strictly elementary classes of large degree are
     connected (`thumann-finiteness-without-finite-type`).

   Then `[[Λ]]` is finitely presented and is its own type (A) actor. Hence `Λ`, and every subgroup
   of `[[Λ]]`, lies in `B_A` and embeds in a finitely presented simple group. If instead the
   spine is finite, Thumann's theorem gives `F_∞`, and the same conclusion follows.
4. **No condition on the carrier's pair orbits.** In 3, `Λ` may have infinitely many orbits on
   pairs of tiles, and on pairs of moves in position.

## Proof

1. **`G_𝒪 ≤ [[Λ]]`.** A fraction `e∘d^{-1}` agrees on each `d`-piece with a composite of the
   `Λ`-local identifications of that piece, of the model tile, and of the matching `e`-piece.
   Composites and inverses of `Λ`-local maps are `Λ`-local. There are finitely many pieces, so
   `e∘d^{-1} ∈ [[Λ]]`.
2. **The operad boundary is `Y`.** Send `y` to the thread of pieces containing it, one for each
   expansion; each expansion's pieces partition `Y`.
   - The map is continuous.
   - It is injective by (B): two points are separated by some piece.
   - It is onto: given a thread `(P_b)`, the sets `P_{b_1} ∩ … ∩ P_{b_r}` contain `P_{b'}` for a
     common refinement `b'` (Ore). So the compact sets `P_b` have the finite intersection
     property, and any point of their intersection maps to the thread.
   - A continuous bijection from a compact space to a Hausdorff one is a homeomorphism.

   So the cylinders of `symmetric-operad-groups-full-cantor-proof` are the pieces, and the
   locality property (Loc) there holds trivially.
   - The action is faithful. If `e∘d^{-1}` is the identity, each `d`-piece equals the
     corresponding `e`-piece, with the same identification. So `e = d`, and `G_𝒪` equals its
     boundary image.
3. **`[[Λ]] ≤ G_𝒪`.**
   - Let `f ∈ [[Λ]]`, equal to `λ_k ∈ Λ` on the pieces `U_k` of a clopen partition.
   - By (C) each `λ_k` lies in `G_𝒪`, so `f` is `G_𝒪`-local.
   - Step 2 of `symmetric-operad-groups-full-cantor-proof` shows that every `G_𝒪`-local
     homeomorphism is a single fraction. It uses only (Ore), symmetry, and the fact that every
     clopen set is a union of pieces of one expansion, which follows from (B) and Ore.
   - So `f ∈ G_𝒪`.
4. **Canonical host.** Immediate from 1.
5. **Reduction.**
   - `thumann-finiteness-without-finite-type` makes `G_𝒪` finitely presented: finite groups are
     `F_∞`, and (G)_2 holds.
   - `G_𝒪` acts faithfully on `Y`.
   - A single nonzero class makes `G_𝒪` clopen transitive
     (`fp-symmetric-operad-groups-lie-in-the-permutational-class`, Statement 3).
   - Statement 4 there gives the type (A) action, and 1 identifies the group with `[[Λ]] ⊇ Λ`.
6. **Pair orbits.** Only (Ore), (B), (C), (G)_2 and the finiteness of the generating data were
   used. ∎

## Why domination is not needed

`edge-split-ore-iff-synchronization-and-tree-domination` proves saturation by dominating an
arbitrary dissection with a split tree that restricts to a split tree on each piece. Step 2 of
the fullness proof avoids this.
- It never needs an expansion adapted to the given pieces `U_k`. It needs only one source
  expansion under the fractions `λ_k`, and one target expansion refining their images.
- Both exist by Ore.
- The assembled fraction `e∘(c∘ω)^{-1}` matches pieces by an arbitrary bijection. That is where
  symmetry is used.

For the edge-split operad, (Sync_m) is established (`unimodular-cells-synchronize-under-edge-splits`),
so (Ore) is equivalent to (TD) there. This theorem therefore recovers the saturation of that node
rather than weakening its hypotheses. What is new is that saturation is a formal property of all
symmetric Ore operads containing their carrier.

## Instances

- **Closed mapping class groups.** Take `Λ = GL_{m+1}(Z)` on `Ŝ_m` and the edge-split operad.
  (C) is `transvections-are-single-carets-of-the-edge-split-operad`, and (B) is cofinality of
  edge-split cells. Under (Ore), `G_E = 𝒯_m`.
  - So in `closed-mcg-bh-via-edge-split-operad` the step through
    `ore-operad-groups-contain-the-derived-full-group` can be replaced by this node. That removes
    the recalled Matui and Powell inputs.
  - The remaining gates are (Ore) and a finite spine, or (G)_2 in its place.
- **The pair orbits of this carrier are infinite.** The unimodular cells form one
  `GL_{m+1}(Z)`-orbit, and the stabilizer `P` of `Δ` is finite (it consists of permutation
  matrices). So orbits of pairs `(Δ, gΔ)` correspond to the double cosets `P \ GL_{m+1}(Z) / P`,
  and there are infinitely many. This holds in every rank `m ≥ 1`. For `m = 1` the invariant is
  the Farey-graph distance between the two intervals.
  - The edge-split operad is still finitely generated with finite transformations, and its
    conjectured finite spine is bounded refinement in the sense of
    `bounded-refinement-operads-reduce-to-their-carriers`.
  - So a carrier that is far from an actor on its tiles is compiled into the actor `𝒯_m` on
    clopens. This happens through the dynamics, not the transformations.
- **Derived full groups.** `ore-operad-groups-contain-the-derived-full-group` becomes a corollary
  in the symmetric case. The operad group is the whole full group, so it contains every subgroup
  of the full group, perfect or not.

## Scope and a sharp question

- The theorem needs symmetry. A planar operad group can be smaller than `[[Λ]]`. It sits inside
  the full group of its symmetrization when that symmetrization satisfies the calculus of
  fractions.
- Statement 3 uses clopen transitivity, so it needs one nonzero class. With several classes it
  gives the full group and finite presentation, but not the type (A) action; this is the
  referee's scope remark on `fp-symmetric-operad-groups-lie-in-the-permutational-class`.
- (C) is the **compiler condition**: every element of the carrier must be a fraction, that is,
  map some expansion onto another piece by piece through the model tiles. For a general carrier
  this is a finite-state condition on its generators relative to the tiles. Nothing here produces
  such operads.
- **Question.** Is there one recursive function bounding the word problem of every group
  `[[Λ]]` arising from a finitely generated, finite-type (finite spine), symmetric Ore operad
  with finite transformations?
  - If yes, then by `complexity-bounded-host-classes-are-not-universal`, finite spines cannot
    carry all decidable inputs through the dynamics.
  - A universal operadic route would then need infinite spines governed by (G)_2. That is the
    regime of `thumann-finiteness-without-finite-type`.

## Lesson for general BH

**Saturation is free, so an operad host is always the carrier's full group.** Once a carrier
group acts by fractions of a symmetric Ore refinement operad, "the moves generate the whole full
group" follows formally from the calculus of fractions. No domination, no Matui, and no
dynamical hypothesis is needed.

So every refinement host is the canonical group `[[Λ ↷ Y]]`, and the operad is only a finiteness
certificate for it. This is the same host shape as Track A's `[[V × Λ⋉X]]`. There quantum rigidity
certifies finiteness; here a finite self-similar tiling of `Y` by `Λ`-local splits (a
`Λ`-substitution) with Ore and (G)_2 does.

Operad hosts carry inputs through two channels:
- **Transformations.** Bounded refinement makes the carrier a Zaremsky actor on its moves.
- **Dynamics.** The carrier acts by fractions, and its pair orbits never enter.

`GL_{m+1}(Z)` on unimodular cones has infinitely many pair orbits and is compiled into `𝒯_m`
through the second channel.
