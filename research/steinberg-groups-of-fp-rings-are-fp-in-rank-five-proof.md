---
rg: 2
id: steinberg-groups-of-fp-rings-are-fp-in-rank-five-proof
kind: route
title: Present St_n of the free ring by iterated commutators of the generators, then add one relator per ideal generator
target: steinberg-groups-of-fp-rings-are-fp-in-rank-five
requires:
  - st-n-of-ring-quotient-adds-one-relator-per-ideal-generator
artifacts:
  - research/artifacts/gq-referee-c-steinberg-finite-presentation-and-kazhdan-theorem.md
  - research/artifacts/gq-referee-a-steinberg-fp-rank-five-direct-proof.md
---

The proof is §2 of `gq-referee-c-steinberg-finite-presentation-and-kazhdan-theorem.md`. Its
proof-gap review is `gq-referee-a-steinberg-fp-rank-five-direct-proof.md`.

1. **The free ring.** For `F = Z<g_1, ..., g_d>` and `n >= 5`, the group with presentation (B1),
   (B2) is isomorphic to `St_n(F)`.
   - The map in one direction sends `y_ij(u)` to `x_ij(u)`.
   - For the inverse, define `X_ij(m)` for monomials `m` by iterated commutators.
   - Then prove by induction on `|m|` three things:
     - `X_ij(m)` does not depend on the split or on the intermediate index;
     - the commutation relations hold;
     - the relations `[X_ij(m), X_jk(m')] = X_ik(mm')` hold.
   - Only the commutation step needs a fifth index.
   - The resulting map `x_ij(Σ c_m m) ↦ ∏ X_ij(m)^(c_m)` respects (R1)–(R3), and it is inverse to
     the first map.
2. **The quotient.** `st-n-of-ring-quotient-adds-one-relator-per-ideal-generator` gives
   `St_n(F/I) = St_n(F)/<<x_12(ρ_1), ..., x_12(ρ_l)>>` for `n >= 4`, where `I = (ρ_1, ..., ρ_l)`.
   Its argument is re-checked in §4 of the gq-referee-c artifact.
