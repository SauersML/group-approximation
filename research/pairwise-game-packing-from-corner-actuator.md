---
rg: 2
id: pairwise-game-packing-from-corner-actuator
kind: route
title: Attach the one-edge acceptance actuator to every relative packing word
target: canonical-positive-density-pairwise-game-overlap-packing
requires:
  - canonical-positive-density-amplified-acceptance-corner-actuator
---

Start with the authenticated packet and freely adjoin
`v_0,...,v_(M-1)`.  For every unordered pair `{i,j}`, attach a fresh copy of
the actuator with ambient return word

```text
r_(ij)=v_i^*v_j.
```

All copies use the same original idempotent `q`; clause 1 of the actuator
keeps its canonical trace equal to the original `alpha`, rather than
intersecting independent controller atoms.  Applying `(ACA1)` to the fixed
finite list gives `(PGO1)` simultaneously after diagonalizing the finitely
many `o(1)` errors.

The relative words automatically satisfy every triangle identity because
they are actual ratios of the vertex words.  No equality among separately
chosen block encoders is imposed away from `q`.

For perfect completeness, take every `v_i` to act as the identity on the
authenticated corner.  Clause 3 of each fresh actuator then extends the
same perfect model; finitely many successive extensions preserve `q!=0` and
the embedded packet.  This proves all three clauses of the target.
