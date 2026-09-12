---
rg: 2
id: bs14-congruence-atom-semigroup-proof
kind: route
title: Factor exact representations through congruence quotients and restrict their irreducibles
target: bs14-global-atoms-are-moving-congruence-restrictions
requires:
  - sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair
  - bs14-native-cells-cross-every-length-cutoff
  - iwahori-uniform-infinitesimal-rigidity
---

The first required claim proves that every finite-dimensional unitary
representation of `A` factors through a finite congruence quotient of odd
level.  Finite-dimensional unitary representations are semisimple, so at
that level the representation is a nonnegative integral sum of irreducibles.
Restriction to `B` is additive, giving `(GAR2)`.  Passing to a common
multiple of two odd levels gives the directed structure.

The even-Weil cross-cutoff claim supplies the explicit irreducible atom
whose restriction is not packetwise.  Finally, uniform infinitesimal
rigidity states its hypothesis at an already chosen congruence
representation; it contains no projection from an arbitrary approximate
tuple to a quotient level.  This proves the stated near/far boundary.

