---
rg: 2
id: decidable-group-ring-has-fp-projective-simple-host
kind: claim
title: Decidable finitely presented group rings embed in rings whose rank-four projective elementary groups are finitely presented and simple
artifacts:
  - research/artifacts/boone-higman-ring-route-repair-2026-09-08.md
  - research/artifacts/boone-higman-projective-finiteness-gate-2026-09-08.md
---

For every finitely presented group H with solvable word problem, there is
a finitely presented unital ring L with a unital injection Z[H] -> L
such that all three conditions hold:

1. ker(St_4(L)->EL_4(L)) is finitely normally generated in St_4(L).
2. Z(EL_4(L)) is finitely generated as a group.
3. PEL_4(L) := EL_4(L)/Z(EL_4(L)) is simple.

By [[projective-elementary-fp-kernel-criterion]], clauses 1 and 2 are
equivalent to finite presentation of PEL_4(L). Thus this formulation is
equivalent to the previous projective-host statement; it exposes exactly
which generating data the construction must provide. No centrality of the
unstable Steinberg kernel is assumed.

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
4. Projectivization cannot repair failure of finite presentation of
   EL_4(L): [[fg-central-extension-of-fp-group-is-fp]] forces the
   elementary group itself to be finitely presented whenever its
   projective quotient is. The exact Steinberg-kernel and center criterion
   above now makes this part of the requested certificate explicit.
5. Projective simplicity already forces L to be a simple ring by
   [[projective-elementary-simplicity-forces-simple-ring]]. This is a
   necessary screen, not a theorem constructing L or proving the converse.
