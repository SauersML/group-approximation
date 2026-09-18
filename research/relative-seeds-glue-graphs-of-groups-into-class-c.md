---
rg: 2
id: relative-seeds-glue-graphs-of-groups-into-class-c
kind: claim
title: Rigid relative seeds (an isolated point with stabilizer exactly C) glue along any graph of groups; so graphs of free or free abelian groups over finitely generated edge groups lie in class 𝒞, and CAP is decided by relative seeds for hard-membership subgroups
requires:
  - tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts
  - locally-finite-splittings-preserve-rigid-sft-compactifications
  - quantum-rigidity-is-product-stable
distinct_from:
  tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts: that glues over trivial edge groups, where the exit of a vertex coset is one element marked by a seed; this glues over arbitrary edge groups, where the exit is a coset aC marked by a relative seed, and recovers tree gluing at C = 1.
  locally-finite-splittings-preserve-rigid-sft-compactifications: that handles finite-index edge groups, where the exit is a finite label; this is the case of relative seeds with finite orbit, and extends it to infinite-index edge groups.
  locally-finite-tree-end-shifts-are-quantum-rigid-sfts: that codes a locally finite tree with finite labels, which bh-star-a shows cannot carry hard inputs; here the tree is locally infinite, and all input complexity sits in the relative seeds on the vertex cosets.
  decidable-groups-embed-in-rigid-sft-compactification-groups: that is (★𝒞) for all decidable groups; this reduces it, along Higman-type towers, to rigid relative seeds for the associated subgroups.
---

**ESTABLISHED** by `relative-seeds-glue-graphs-of-groups-proof` (lane bh-invent-03, 2026-09-18; elementary lane
proof, not reviewed; no priority claimed). Quantum families are Q1–Q3 of
`fp-v-times-subshift-full-groups-force-quantum-rigidity`, over a fixed field `k`.

## Definition

Let `A` be finitely generated and `C ≤ A`. A **rigid relative seed** for `(A, C)` is an SFT `Y ⊆ Σ^A` together with a
pattern `π` on a ball `B_(R_0)`, such that:
- (RS1) `{y ∈ Y : y|_(B_(R_0)) = π} = {y_*}` and `Stab(y_*) = C`, so `y_*` has seeds exactly on `C`;
- (RS2) `Y` is the orbit closure of `y_*`;
- (RS3) `Y` is `D`-quantum rigid for all large `D`.

Write `(A, C) ∈ 𝓡`. Special cases:
- `(A, 1) ∈ 𝓡` iff `A ∈ 𝒞`: an SFT compactification.
- `(A, A) ∈ 𝓡` always: the one-point shift.
- `(A, C) ∈ 𝓡` whenever `[A : C] < ∞`: the finite shift on `A/C`.

## Statement

**1. Gluing.** Let `𝔾` be a finite graph of finitely generated groups and `Λ = π_1(𝔾)`. Suppose that for every
oriented edge `ε`, the image `C_ε` of its edge group satisfies `(V_(o(ε)), C_ε) ∈ 𝓡`. Then for every vertex `u` and
every `C` with `(V_u, C) ∈ 𝓡`, we have `(Λ, C) ∈ 𝓡`. In particular:
- `Λ ∈ 𝒞` as soon as one vertex group is in `𝒞` (take `C = 1`);
- `(Λ, V_u) ∈ 𝓡` for every vertex `u`, with no vertex group in `𝒞` (take `C = V_u`).

**2. Induction.** If `C ≤ H ≤ A` with `[A : H] < ∞` and `(H, C) ∈ 𝓡`, then `(A, C) ∈ 𝓡`.

**3. Membership is consumed.** Assume `A` has solvable word problem and `(A, C)` satisfies (RS1) for some SFT;
(RS2) and (RS3) are not needed. Then `y_*` is computable, and so membership in `C` is decidable, uniformly from the
word problem of `A` and the finite data. In a rigid relative seed, the forced point **is** a membership oracle
for `C`.

## Corollaries

- (a) **Free groups.** Every finitely generated `C ≤ F_n` has `(F_n, C) ∈ 𝓡`.
  - Proof: by M. Hall's theorem, `C` is a free factor of some finite-index `H = C * D`. Apply 1 to `C * D` with
    `C = V_u` (edge group trivial, with seeds of free groups), then apply 2.
  - The forced point is finite-state: tree pointers toward one `C`-vertex, like the lifted Stallings core of `C`.
- (b) **Free abelian groups.** Every `C ≤ Z^m` has `(Z^m, C) ∈ 𝓡`.
  - Proof: in a Smith basis, `C = d_1 Z × ⋯ × d_j Z × 0^(m−j)`. Take the product of the finite shifts `Z/d_i`
    with `C_Z^(m−j)`. The product point is isolated with stabilizer `C`, and it is rigid by
    `quantum-rigidity-is-product-stable`.
- (c) **Graphs of free and free abelian groups.** Every finite graph of groups with free or free abelian vertex
  groups and finitely generated edge groups has its fundamental group in `𝒞`. Examples:
  - all HNN extensions of free groups over finitely generated associated subgroups, with any finite number of
    stable letters; this includes the modular-machine groups of Aanderaa–Cohen (recalled, not re-read);
  - tubular groups, BS(m,n), and free-by-cyclic groups.
- (d) **Earlier results as special cases.** Tree gluing is the case of trivial edge groups;
  `locally-finite-splittings-preserve-rigid-sft-compactifications` is the case of finite-index edge groups.

## What this does to CAP (SYNTHESIS v6, gate 1)

**Splittings cost nothing once relative seeds exist.** (★𝒞) for `G` therefore follows from rigid relative seeds for
the associated subgroups of any Higman–Clapham tower containing `G`.

**The first rung is done.** The first rung of an Aanderaa–Cohen tower is an HNN extension of a free group, which is
in `𝒞` by (c).

**The next rung is the test.** It extends that group over finitely generated subgroups whose membership problem
encodes the machine: halting in the r.e. case, and a decidable set of arbitrary complexity in Clapham's version
(recalled, not re-read). By 3, a rigid relative seed there must compute that membership.

**The sharp question:** can a rigid relative seed encode a membership problem of arbitrary complexity?
- Every relative seed recorded so far is finite-state: the Stallings cores, finite `A/C` shifts, trees, and
  products.
- **If yes,** (★𝒞) follows along the tower, so CAP is false. The coordinator should check that the remaining tower
  steps are splittings.
- **If no,** CAP becomes a theorem about the complexity of rigid relative seeds, provable for the stabilizers of
  their forced points.

## Lesson for general BH

The E1′+E2 gate is **local to subgroups**. Gluing along a graph of groups needs, for each edge group `C ≤ V`, only a
locally checkable rigid marking of one coset of `C`. Minimality, topological freeness and rigidity along the
Bass–Serre tree are free.
- **Hardness has one home.** A Higman–Clapham embedding is built from splittings, and the only non-finite-state
  object it needs is a rigid relative seed for a subgroup whose membership is as hard as the input's word problem.
- **Rigidity pays for decidability.** By item 3, the forced point is that membership oracle.
- **CAP is one question.** Can compression-rigid, locally forced configurations compute? That is, is there a rigid
  relative seed whose stabilizer has membership outside every fixed class?
- **Suggested first test.** `(K_M, R_0)` for a trivial modular machine, with lanes bh-free-56 and bh-star-a.
