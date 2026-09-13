---
rg: 2
id: sl3z-coherence-forces-rfrs-cd2-subgroups-free-by-cyclic-proof
kind: route
title: Apply the dimension-two RFRS coherence characterization to subgroups of SL_3(Z)
target: sl3z-coherence-forces-rfrs-cd2-subgroups-free-by-cyclic
requires:
  - virtually-rfrs-cd2-coherence-characterization
artifacts:
  - research/artifacts/zp-sl3z-coherence-non-dense-2026-09-13-part2.md
---

1. Coherence passes to subgroups, so `H` is coherent.
2. `virtually-rfrs-cd2-coherence-characterization` applies to finitely
   generated virtually RFRS groups with `cd_Q <= 2`. For `k = Q` it makes
   coherence equivalent to `b_2^(2)(H) = 0` and to `H` being virtually
   free-by-cyclic.
3. **Contrapositive.** A finitely presented virtually RFRS `H` with
   `cd_Q(H) <= 2` is of type FP over `Q`, so `χ(H)` is defined. For infinite
   `H`, `b_0^(2)(H) = 0`, so `b_2^(2)(H) - b_1^(2)(H) = χ(H)`. Hence
   `χ(H) > 0` forces `b_2^(2)(H) > 0`, so `H` is incoherent, and therefore so
   is `SL_3(Z)`.

This is Consequence 7.1 of the artifact.
