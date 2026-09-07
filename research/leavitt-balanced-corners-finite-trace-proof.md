---
rg: 2
id: leavitt-balanced-corners-finite-trace-proof
kind: route
title: Replay the cubic pair through the general finite-precision trace invariant
target: leavitt-balanced-corners-separated-modulo-four
requires:
  - finite-precision-lifted-trace-obstruction
  - leavitt-trace-balanced-nested-idempotents
artifacts:
  - experiments/kaplansky_trace_certificate.py
  - experiments/test_kaplansky_trace_certificate.py
  - research/artifacts/kaplansky-trace-certificates.json
  - research/artifacts/kaplansky-finite-precision-trace-2026-09-07.md
---

The second prerequisite supplies independent commuting cubic elements g,h
in Q, hence an embedded H=C_3 x C_3, and the pair
e=[g]+[g^2], f=e([h]+[h^2]). Over (Z/4)[H] set

    E=2[1]+[g]+[g^2],       C=2[1]+[h]+[h^2],       F=EC.

Using g^3=h^3=1, E^2=E and C^2=C. They commute, so F^2=F, and these
are the required reductions. Independence of g,h gives T(E)=2 and T(F)=0
modulo four. The first prerequisite excludes equivalence, including after
any common projective stabilization in the full ambient F_2[Q].

For the p-adic refinement, E=(2-g-g^2)/3 and C=(2-h-h^2)/3 are the
corresponding idempotent lifts over Z_2[H]. Their traces are 2/3 and 2/3,
whereas T(EC)=4/9 because H is the direct product of the two cubic groups.
Thus the difference is 2/9. These elementary identities prove the whole
target statement without relying on a search or on code correctness.

The exact replay checks the finite table, the idempotent lifts, and their
traces at precisions 1, 2, and 5. A separate finite regular representation
computes ranks 6 and 4 over F_2 and checks the normalized values 2/3 and 4/9.
The code certifies the finite arithmetic; the named prerequisite, not the
table's name, supplies the embedding H<=Q. This adds an independently
replayable route to an already established refutation, not a new refutation
of Kaplansky's conjecture.
