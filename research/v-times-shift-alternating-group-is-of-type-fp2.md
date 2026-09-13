---
rg: 2
id: v-times-shift-alternating-group-is-of-type-fp2
kind: claim
title: "The alternating full group of V times the full two-sided shift is of type FP_2"
---

With the notation of `v-times-shift-alternating-group-restrictions-are-simple`,
the group `A(G)` for `G = G_V × (Z ⋉ {0,1}^Z)` is of type FP_2 over `Z`.
Finite presentability would be stronger than needed.

## Attempts

- 2026-09-13 (lane z1-20-simple-fp2): `A(G)` is finitely generated
  (Nekrashevych, arXiv:1511.08241: expansive groupoids). It contains
  - copies of `V` controlled by clopen sets of the shift coordinate, conjugated
    around by the shift;
  - shifts controlled by cylinders of `C`;
  - the abelian group `C(C, Z)` of controlled shift exponents, normalized by `V`.
- It is a subgroup of the Brin–Thompson group `3V`. Split
  `{0,1}^Z = {0,1}^N × {0,1}^N` into past and future. The shift then becomes
  the baker's map `(p, f_0 f') ↦ (f_0 p, f')`, an element of `2V`. So `G` is an
  open subgroupoid of the groupoid of `3V`, and `[[G]] ≤ 3V`.
- No finiteness proof is known. A Stein–Farley-type complex for the germs of
  `G` (prefix trees in the `C` coordinate, clopen partitions with shift labels
  in the `Σ` coordinate) with Brown's homological criterion is the natural
  attempt. The needed input is homological 1-connectivity of descending links
  over a Z-labelled partition complex, which has not been checked.
- Dies if: some quotient or retract of `A(G)` is visibly not FP_2, for example a
  lamplighter-like `C(Σ, V) ⋊ Z` retract. None has been found; restricting to a
  periodic orbit gives Higman–Thompson-type quotients, which are of type F_∞.
