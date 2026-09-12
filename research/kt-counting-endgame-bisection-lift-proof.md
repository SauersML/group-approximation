---
rg: 2
id: kt-counting-endgame-bisection-lift-proof
kind: route
title: Lean proof of the finite counting endgame
target: kt-counting-endgame-bisection-lift
requires: []
artifacts:
  - GroupApproximation/KunThom/CountingEndgameCompletion.lean
  - GroupApproximation/KunThom/CountingEndgameLift.lean
  - GroupApproximation/KunThom/CountingEndgameWeights.lean
  - GroupApproximation/KunThom/CountingEndgameRestrict.lean
---

A derivation in Lean. The four modules are imported by `GroupApproximation.lean`
and built green by the Bowen–Chapman probe (tags 0912-125654-51047,
0912-131259-52910, 0912-132636-54185 and 0912-133947-28849).

1. **Counting** (tex 1245–1276). If two objects are disconnected but their
   images are connected, both source orbits sit inside one image orbit
   (`ComponentCountingNormalization.card_orbit_inter_add_le`). An integer index
   below `2` makes the faithful isotropy map onto
   (`ComponentCountingNormalization.map_bijective_of_isotropy_lt_two_mul`), and
   then the Hom-set map is onto because Hom-sets are torsors.
2. **Completion** (tex 1287–1292). An object map that is injective on `S` and
   keeps `S` inside its orbits extends to an orbit-preserving permutation. The
   proof is induction on the number of objects outside `S`. An unselected
   source `X₀` always has an unselected target in its orbit `Ω`, because the
   image of `S ∩ Ω` has exactly as many objects as `S ∩ Ω`. Arrows off `S` are
   arbitrary, and they exist by connectedness.
3. **Weights** (tex 1140–1156 and 1294–1313). The clean-orbit bound is a double
   count over orbits, weighting each vertex by the inverse size of its orbit.
   The completion and preimage bounds sum over injective images.
