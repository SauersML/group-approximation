---
rg: 2
id: v-rank-trivial-plus-regular-on-cylinder-groups-proof
kind: route
title: Rank functions on F[V] are trivial plus regular on finite subgroups, via the odd torsion law on a normalized odd-cycle group
target: v-rank-functions-are-trivial-plus-regular-on-cylinder-groups
requires:
  - v-rank-models-are-trivial-plus-free-on-odd-cycle-trees
  - v-rank-torsion-constant-equals-global-fixed-rank
  - finite-subgroups-of-thompson-v-permute-a-canonical-partition
artifacts:
  - research/artifacts/thompson-v-rank-functions-regular-on-cylinder-groups-2026-09-12.md
  - research/artifacts/w3-vf-linear-verification-2026-09-12.md
---

The proof is Section 1 of the artifact (w7-v-cycle-c2). `w3-vf-linear` re-derived it in Section 32 of its verification
artifact.

1. **Auxiliary group.** Fix an odd prime `p != char F`. In each `G`-orbit on the partition `Pi`, put a clopen `p`-cycle
   inside `[u0]` and transport it by `G`. The result is `Q = (Z/p)^Pi`, which `G` normalizes by permuting coordinates.
   Every nonidentity element of `Q` is a clopen `p`-cycle, so `Q` is a clopen-cycle subgroup.
2. **Characters.** The torsion law and the torsion constant give `rk(e_chi) = phi_V [chi = 1] + (1 - phi_V) p^(-|Pi|)`
   after scalar extension. The orbit sums `f_O` are orthogonal idempotents that commute with `F[G]`.
3. **Trivial character.** `{1 - [c_v], 1 - [g]}` and `{1 - e, e(1 - [g])}` generate the same left ideal, which gives
   `rk col(e(1 - [g])) <= rk(e) - phi_V`. So `rk(eA)` is within `2n(1 - phi_V) p^(-|Pi|)` of `phi_V rank eps(A)`.
4. **Free nontrivial orbits.** `f_O` is equivalent to `I_|G| ⊗ e_chi`, and `f_O A` becomes `Reg(A) ⊗ e_chi`.
5. **Count.** At most `(|G| - 1) p^(|Pi| - 1)` characters are not free. The total error is at most `2n|G|/p`, so let
   `p -> infinity`.

**Scope.** Every finite subgroup of `V` is a cylinder group by
`finite-subgroups-of-thompson-v-permute-a-canonical-partition`.
