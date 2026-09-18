---
rg: 2
id: cuntz-stabilized-full-groups-contain-their-own-squares
kind: claim
title: The topological full group of any Cuntz-stabilized ample groupoid, and its commutator subgroup, contain their own direct squares, so every group hosted there has its square in the same host
distinct_from:
  leavitt-pair-unit-hosts-contain-their-own-squares: that is the ring version (units of rings with a Leavitt pair); this is the groupoid version, the one used by the group-side hosts on main.
  twisted-btb-clopen-action-is-type-a: that is the special case of twisted Brin--Thompson groups, whose clopen stabilizers are SV_G x SV_G; this covers every full group of a groupoid of the form G x R_2.
  finitely-coded-cantor-actions-give-type-a-hosts: that builds type (A) actions and finite presentation for such full groups; this records only the squaring property, which needs no finiteness hypothesis.
---

**ESTABLISHED** (lane proof, bh-major-product, 2026-09-18; elementary; not independently
reviewed; no priority claimed).

## Statement

Let `𝒢` be an ample groupoid with unit space `Y`. Let `R_2` be the Cuntz groupoid on
`C = {0,1}^N`, whose arrows are the germs of prefix replacements `u w ↦ v w`. Put
`H = 𝒢 × R_2` on `Y × C`, and let `Φ = [[H]]` be its topological full group. Then:

1. For `i = 0, 1` there is an injective homomorphism `ι_i : Φ → Φ` with support in `Y × [i]`.
2. `ι_0(Φ)` and `ι_1(Φ)` commute, so `Φ × Φ ≤ Φ`.
3. The same holds for the commutator subgroup `D(Φ)`, and for every subgroup: if `G ≤ Φ`,
   then `G × G ≤ Φ`, and if `G ≤ D(Φ)`, then `G × G ≤ D(Φ)`.

## Proof

- **The cone shift.** The prefix map `z_i : C → [i]`, `w ↦ i w`, is a compact open bisection
  of `R_2` from `C` onto the cone `[i]`. So `Z_i = Y × z_i` is a compact open bisection of `H`
  from `Y × C` onto `Y × [i]`.
- **The two copies.** For `g ∈ Φ` with full bisection `B`, set
  `ι_i(g) = Z_i B Z_i^(-1) ⊔ (units over Y × [1 − i])`. This is a compact open bisection with
  source and range all of `Y × C`, so it lies in `Φ`. On `Y × [i]` it acts as `z_i g z_i^(-1)`;
  on `Y × [1−i]` it is the identity.
- **Homomorphism and injectivity.** `g ↦ z_i g z_i^(-1)` is conjugation by a homeomorphism
  onto its image, so it is an injective homomorphism into the homeomorphisms of `Y × [i]`.
- **Commuting.** `ι_0(g)` and `ι_1(h)` have disjoint supports, so they commute.
- **Commutator subgroups.** `ι_i` maps commutators to commutators, so it maps `D(Φ)` into
  `D(Φ)`. Restricting to a subgroup gives item 3.

## Consequences on main

- **The simple hosts.** Every simple host on main of the form `D([[𝒢 × R_2]])` contains its
  own square. These are the hosts of `finitely-coded-cantor-actions-give-type-a-hosts` and
  `degree-category-full-groups-stabilized-have-type-a-actions`, simple by Matui when `𝒢 × R_2`
  is minimal, effective and purely infinite. So for every group `G` placed there, `G × G` lies
  in the same finitely presented simple group. This is (SQ) for all such `G` with no new
  finiteness input.
- **Examples:** the Ã₂, tree-product and Euclidean-building lattice hosts, and the
  group-side master-route host `boone-higman-via-v-times-aperiodic-sft-full-groups`. This
  agrees with the known closure of `B_A` under finite direct products.
- **General form (same proof).** The product structure is not needed. Let `H` be any ample
  groupoid on `X` with two compact open bisections `Z_0, Z_1` whose source is all of `X` and
  whose ranges are disjoint. Then `[[H]] × [[H]] ≤ [[H]]`, and likewise for `D([[H]])`.
  - Example: `CT_P(Z)` and the RCWA hosts on main use the canonical box maps
    `n ↦ 2n` and `n ↦ 2n + 1` from `Z` onto `0(2)` and `1(2)`.
  - Non-example: suppose the groupoid has an invariant probability measure `μ`. A bisection
    `Z` with source `X` has `μ(r(Z)) = μ(X) = 1`, so two such bisections can't have disjoint
    ranges. The full groups of minimal Cantor `Z`-systems are like this, so they are not
    self-square in this way.

## Lesson for general BH

Cuntz stabilization is a squaring device. Every host produced by the swarm's machine (a coded
groupoid, times `R_2`, then the commutator subgroup) is a group that contains its own square.
This is the groupoid face of the Leavitt corner map in
`leavitt-pair-unit-hosts-contain-their-own-squares`. So product closure is never a separate gate
for a constructive Boone--Higman route through these machines: the closure comes with the
route. An obstruction to (SQ) would have to be an fp simple group that embeds in no
self-square fp simple group.
