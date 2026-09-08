---
rg: 2
id: decidable-group-ring-has-fp-projective-simple-host
kind: claim
title: Decidable finitely presented group rings embed in rings whose rank-four projective elementary groups are finitely presented and simple
artifacts:
  - research/artifacts/boone-higman-ring-route-repair-2026-09-08.md
---

For every finitely presented group H with solvable word problem, there is
a finitely presented unital ring L with a unital injection Z[H] -> L
such that

    PEL_4(L) := EL_4(L) / Z(EL_4(L))

is a finitely presented simple group.

**OPEN.** This is a corrected sufficient hypothesis for the ring approach
to Boone--Higman. It restricts the coefficients to the actual torsion-free
additive group rings and explicitly requires both properties of the
projective target. It does not assert that ring simplicity alone supplies
them. No necessity or equivalence to Boone--Higman is claimed.

## Attempts

1. The unrestricted finite-fullness theorem is refuted by Z/6Z through
   [[ring-simple-envelope-characteristic-obstruction]]. Integral group
   rings avoid that obstruction, but the endomorphism construction gives
   no finite presentation of the resulting ring or projective group.
2. Taking EL_4(L) itself is excluded by
   [[rank-four-elementary-center-obstructs-simplicity]]. Passing to its
   center quotient avoids the exhibited involution but does not prove
   projective simplicity or finite presentation. Even if EL_4(L) is
   known finitely presented, finite normal generation of its full center
   still has to be established to invoke the quotient criterion.
3. Making one coefficient full supplies the explicit CK envelope. It
   leaves proper ideals and does not establish the projective conclusions.
