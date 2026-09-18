---
rg: 2
id: trees-of-groups-with-realizable-edges-realize-vertices
kind: claim
title: Relative realizability of subgroup pairs is transitive, descends to intermediate subgroups and is closed under amalgamation, so every vertex group of a tree of groups whose edge groups are realizable in both adjacent vertex groups (plus free-group loop edges) is realizable in the fundamental group
distinct_from:
  continuous-free-chain-unions-have-gd-two: its Lemma 2 realizes a vertex group of a graph of groups with free edge groups; this allows non-free edge groups along a maximal tree, requiring only that each edge group be realizable in both neighbours.
  relative-eg-pair-iff-aleph-one-star-amalgam-has-gd-two: that is the per-pair engine (RP(H,G) iff gd of the aleph_1-fold amalgam is 2) and supplies the swap lemma used here; this is a closure theorem for RP under transitivity, amalgams and trees.
  relative-eg-pair-base-meets-its-conjugates-in-free-groups: that is a necessary algebraic condition on admissible pairs; this is a sufficient geometric condition, and the two together bracket the minimal-counterexample profile.
artifacts: []
---

**ESTABLISHED** through `trees-of-groups-with-realizable-edges-realize-vertices-proof`. Unreviewed. No novelty claimed with confidence; the ingredients are the swap lemma and Whitehead's gluing theorem.

## Notation

`RP(C,B)` for `C ≤ B` (any cardinality): some 2-dimensional aspherical `X` with `π_1 X ≅ B` has an aspherical subcomplex `K` with `K ↪ X` inducing `C ≤ B`. By the swap lemma of `relative-eg-pair-iff-aleph-one-star-amalgam-has-gd-two` (whose proof uses no countability), `RP(C,B)` implies that every 2-dimensional `K(C,1)` extends to such an `X`.

## Statement

- **(T1) Transitivity.** `RP(A,B)` and `RP(B,C)` imply `RP(A,C)`.
- **(D) Descent.** If `H ≤ G ≤ G'` and `RP(H,G')`, then `RP(H,G)`. Hence `RP(H,G)` holds iff `RP(H,G')` holds for *some* overgroup `G' ≥ G`; and `RP(H,G) ⇔ RP(H, Γ_κ(H,G))` for every `κ ≥ 1`.
- **(T2) Amalgams.** If `RP(C,A)` and `RP(C,B)`, then `RP(A, A *_C B)` and `RP(B, A *_C B)`.
- **(R) Trees.** Let `𝒯` be a tree of groups (any cardinality) with vertex groups `G_v` and edge groups `C_e`, and suppose `RP(C_e, G_u)` and `RP(C_e, G_w)` for every edge `e = (u,w)` (and `gd G_v ≤ 2` if `𝒯` is a single vertex). Then `RP(G_v, π_1 𝒯)` for every vertex `v`.
- **(R') Trees plus free loops.** Let `𝒢` be a graph of groups with a maximal tree `T` satisfying the hypothesis of (R), and with free edge groups on the edges outside `T`. Then `RP(G_v, π_1 𝒢)` for every vertex `v`.
- **(M3) Peripheral 3-manifold pairs.** Let `M` be a compact orientable aspherical 3-manifold with an incompressible boundary component `F` of genus `≥ 1`, `H = π_1 F ≤ G = π_1 M`. Then `(H,G)` is admissible (`pd I_{G/H} ≤ 1`) iff `RP(H,G)` iff `∂M ≠ F`. So the natural "peripheral" candidates suggested by `relative-eg-pair-base-meets-its-conjugates-in-free-groups` all either realize or fail the pd hypothesis.

## Consequence for the minimal counterexample

The base `H` of a pair `(H,G)` whose `ℵ_1`-fold amalgam is an Eilenberg--Ganea counterexample is not a vertex group of any splitting as in (R') of **any overgroup** `G' ≥ G` (by (D)), and no 2-dimensional `K(G',1)` of any overgroup has an aspherical `π_1`-injective subcomplex carrying `H`. Failure of RP propagates up to every overgroup; realization may be proved in any convenient overgroup. Since `RP(C,B)` holds whenever `C` is free and `gd B ≤ 2` (Lemma 1 of `continuous-free-chain-unions-have-gd-two-proof`), and whenever `C = B` with `gd B ≤ 2`, this subsumes item 2 of the profile for tree-shaped splittings and extends it to hierarchies: splittings whose edge groups are themselves realizable, recursively (by (T1)), e.g. edge groups that are vertex groups of free-edge splittings of the adjacent vertex groups.

By (T1) and (D) together, for a realizable tower `RP(G,G')` one has `RP(H,G) ⇔ RP(H,G')`.
