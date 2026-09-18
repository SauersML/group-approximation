---
rg: 2
id: boone-higman-via-v-times-rigid-topfree-sft-full-groups
kind: route
title: Put the group in a finitely presented group carrying a rigid minimal topologically free SFT, then take the alternating full group of V times its transformation groupoid (Track A, group side, topologically free form)
target: boone-higman-conjecture
requires:
  - decidable-groups-lie-in-fp-groups-with-rigid-topfree-sfts
  - v-times-rigid-topologically-free-sft-full-groups-are-fp
  - v-times-ample-full-groups-are-generated-by-transpositions
  - nekrashevych-symmetric-and-alternating-full-groups
  - fp-v-times-minimal-action-full-groups-have-type-a-actions
---

**Route** (lane bh-g3-topfree, 2026-09-18). This is the group side of Track A of
`research/artifacts/gq-bh-synthesis-master-route.md`, with gate E1 relaxed to topological freeness
(E1′) and gate E3 restated accordingly (E3′). It refines `boone-higman-via-v-times-aperiodic-sft-full-groups`,
whose premise P2 is refuted (golden–silver), by adding rigidity and relaxing freeness.

Let `G` be finitely generated with solvable word problem.

1. **Existence and rigidity (E1′ + E2).** By `decidable-groups-lie-in-fp-groups-with-rigid-topfree-sfts`,
   choose `Λ >= G` finitely presented and a nonempty minimal topologically free SFT `X` over `Λ`
   that is quantum rigid. Without loss of generality `G` is infinite, so `X` is a Cantor space
   (`master-route-needs-only-topological-freeness`, Setting).
2. **The host groupoid.** `T = G_V × (Λ ⋉ X)` is ample, Hausdorff and minimal. It is effective, since
   `Λ ↷ X` is topologically free (`master-route-needs-only-topological-freeness`, item (2)).
3. **`G ≤ A(T)`.** `λ -> ((c, x) ↦ (c, λx))` embeds `Λ` in `F(T)`, because topological freeness
   implies faithfulness. And `F(T) = A(T)` by `v-times-ample-full-groups-are-generated-by-transpositions`.
4. **Simple.** Nekrashevych's Theorem 4.1 (`nekrashevych-symmetric-and-alternating-full-groups`).
5. **Finitely presented (E3′).** `v-times-rigid-topologically-free-sft-full-groups-are-fp`.
6. **Type (A).** `fp-v-times-minimal-action-full-groups-have-type-a-actions`. So every subgroup of `Λ`
   lies in `B_A`, and the route gives PBH, not only BH.

So `G` embeds in the finitely presented simple group `A(T)`. ∎

## Status

**OPEN** through its first two premises. Steps 2–4 and 6 are established and use no freeness.
- **Instances where the whole route fires:** subgroups of products of tree groups
  (`v-times-tree-boundary-full-groups-are-f-infinity`) and Ã₂ lattices
  (`a2-lattice-boundary-skew-shifts-are-quantum-rigid`). Boone–Higman was already known there.
- **Comparison with the ring side** (`boone-higman-via-leavitt-units-of-rigid-topologically-free-sfts`).
  - This route needs no K-gate, no Farrell–Jones instance and no Khanh import.
  - It allows torsion in isotropy.
  - In exchange it needs the group-side finiteness E3′, where the ring side has the established
    `quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products`.

## Lesson for general BH

On the group side, freeness of the SFT was never used. Only effectiveness and minimality are
consumed after finite presentation, so Track A should be run in this form. Its remaining content is
then two statements about one object: a rigid compression coding over an overgroup of the input
(E1′ + E2), and the Stein–Farley finiteness of its V-stabilized full group (E3′), which is a theorem
for every known instance.
