---
rg: 2
id: free-group-boundary-shifts-are-quantum-rigid
kind: claim
title: The end shift of a free group, coded over the group itself, is quantum rigid at every scale over every field, and so is its product over a product of free groups
distinct_from:
  boundary-crossed-product-is-a-leavitt-path-algebra: that identifies LC(∂F_d,k) ⋊ F_d with a Leavitt path algebra, so the crossed product is finitely presented; this proves quantum rigidity of the end shift itself (conditions Q1-Q3), the rank-one case left unchecked in euclidean-building-boundary-shifts-are-quantum-rigid.
  euclidean-building-boundary-shifts-are-quantum-rigid: that poses rigidity of chamber-boundary shifts of Euclidean-building lattices (rank two and higher); this settles the rank-one case, trees, by a monotone-chain argument.
  quantum-rigidity-is-product-stable: that proves products of rigid SFTs are rigid; this supplies rigid factors over free groups, so the product is a rigid minimal topologically free SFT over the one-ended non-amenable group F_m x F_n.
  permutive-triangle-sfts-are-quantum-rigid: that proves rigidity by propagating local determinism; the end shift is not deterministic in any direction, and its rigidity comes from monotone chains of projections (compression) instead.
---

**ESTABLISHED** through `free-group-boundary-shift-rigidity-proof` (lane bh-g2-fixedpoint-b,
2026-09-18; elementary lane proof, not reviewed; no priority claimed). Quantum rigidity is as in
`fp-v-times-subshift-full-groups-force-quantum-rigidity` (conditions Q1–Q3).

## Setting

`Λ` is a group with a finite symmetric generating set `S` whose Cayley graph `T` is a tree of
degree `|S| >= 3`. Examples: `F_n` with a free basis (`n >= 2`), and free products of copies of `Z` and
`Z/2` with their standard generators.

The **end shift** `X_∂ ⊆ S^Λ` is cut out by one rule on each edge `{g, gs}`:

> exactly one of `x(g) = s` and `x(gs) = s^(-1)` holds.

Read `x(g) = s` as "the arrow at `g` points along the edge labelled `s`".

## Statement

1. **Coding.** Each `x ∈ X_∂` gives every vertex exactly one out-edge and orients every edge, so the
   out-arrows from any vertex form a ray, and all these rays share a tail. Hence `x` determines an
   end `ξ(x) ∈ ∂T`, and `x ↦ ξ(x)` is a `Λ`-equivariant homeomorphism `X_∂ ≅ ∂T`. The action is
   minimal and topologically free. It is **not** free: every element of infinite order (every nontrivial element of `F_n`) fixes its two ends.
2. **Rigidity.** For every `D >= 1` and every field `k`, `X_∂` is `D`-quantum rigid.
3. **Products.** With `quantum-rigidity-is-product-stable`:
   - `X_∂(F_m) ⊠ X_∂(F_n)` is `D`-quantum rigid over `F_m × F_n`, and minimal and topologically
     free there. So a one-ended, non-amenable, torsion-free, finitely presented group carries a
     quantum-rigid minimal topologically free SFT.
   - For any group `Λ_0` and SFT `X_0` over it, `X_0 ⊠ X_∂` over `Λ_0 × F_n` is rigid iff `X_0` is.

## Calibrations

- **Ring side.** With `quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products`, item 2 makes
  `LC(∂F_n, k) ⋊ F_n` finitely presented. That agrees with its Leavitt path algebra presentation
  (`boundary-crossed-product-is-a-leavitt-path-algebra`). So outside `Z^2` there is at least one
  shift where "finitely presented crossed product" and "quantum rigid" hold together.
- **Walls.** Any two modifications of `x_ξ` differ from it on sets that both contain a tail of the
  ray to `ξ`. So the far-modification lemma of
  `minimal-sfts-with-a-finite-modification-are-not-quantum-rigid` never fires, as it must not. The
  single free branch of `quantum-rigid-sfts-over-products-have-a-single-free-branch` is the branch
  containing `ξ`.
- **Not deterministic.** `x(g)` is not determined by the configuration on any one branch at `g`. So
  this is not the permutive/deterministic mechanism.

## Lesson for general BH

- **Compression gives rigidity.** Over non-amenable groups, quantum rigidity has the mechanism the
  `Z^2` heuristic said was missing (`free-minimal-z2-sft-is-quantum-rigid`, "Heuristic against"). The
  edge rule forces the orientation projections along every geodesic into a **monotone chain**
  `Q_1 ≤ Q_2 ≤ …`. Monotone chains of projections commute with no further input. This is the
  operator shadow of the paradoxical decomposition behind the Leavitt presentation.
- **So rigidity is not the obstruction over non-amenable groups; freeness is.** The mechanism rides on
  hyperbolic elements fixing ends, and every nontrivial element of `F_n` has fixed points on
  `X_∂`. Over `F_n` no SFT is free anyway (Piantadosi, as used in
  `deterministic-time-lifts-inherit-quantum-rigidity`). Over `F_m × F_n` the boundary product is rigid
  and minimal but not free.
- **For gate G2 over `Λ_0 × F_n`.** The master route's crux is therefore sharper than "a rigid free
  minimal SFT". It is "couple a `Λ_0`-fibre to a compression direction so that the fibre inherits
  chain rigidity *and* the coupling kills the fixed points". Fixed-point hierarchies are one proposed
  source of such a coupling; the boundary shift shows the rigidity half needs no hierarchy.
- **Ring-side remark (a pointer, not a proof).**
  - *Where freeness is used.* The (K) premise uses freeness only against finite-order isotropy (the
    trace screen in `free-action-leavitt-tensor-hosts-have-trivial-k1-k2`), and its known case 1 (a
    torsion-free Farrell–Jones `Λ`, any action) covers `F_m × F_n`.
  - *What that allows.* A rigid, minimal, topologically free SFT with torsion-free isotropy may be
    enough on the ring side.
  - *What is unchecked.* Whether step 2 of `boone-higman-via-leavitt-units-of-rigid-sft-overgroups`
    (central simplicity) survives topological freeness.

## Open

- **The Roller-boundary analogue.** Take a group acting simply transitively on the vertices of a CAT(0)
  cube complex (RAAG Salvetti covers). Code halfspace orientations, requiring the out-hyperplanes at
  each vertex to span a cube. Is this shift rigid? The obstacle is whether local consistency forces
  global ultrafilter consistency.
- **Coupling.** Is there a quantum-rigid **free** minimal SFT over `F_m × F_n`? Any such shift has a
  single free branch at every slab (`quantum-rigid-sfts-over-products-have-a-single-free-branch`), so
  it is "end-directed" in each factor like `X_∂`, and it must also kill the ends' fixed points.

DERIVATION
free-group-boundary-shift-rigidity-proof
