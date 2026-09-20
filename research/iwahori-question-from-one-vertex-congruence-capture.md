---
rg: 2
id: iwahori-question-from-one-vertex-congruence-capture
kind: route
title: Capture one vertex, transfer congruence across the Iwahori edge, then apply the congruence-capture reduction
target: iwahori-local-global-defect-question
requires:
  - iwahori-one-vertex-congruence-capture
  - iwahori-congruence-capture-transfers-across-one-edge
---

Let `def(pi_n) -> 0`. The one open prerequisite gives `A_+(pi_n) -> 0`.
Consequence 1 of `iwahori-congruence-capture-transfers-across-one-edge` then
gives `D(pi_n) -> 0`. That consequence combines (CT1) with the uniform
congruence-pair repair. Arguing by contradiction over sequences produces the
modulus `f`.

This route is not a restatement of the capture statement (DCC3) of
`dv-distance-is-defect-plus-congruence-capture`. That statement needs *both*
vertices to be captured, jointly, by exact congruence pairs. Here the
second vertex and the pairing are supplied by induction and Selberg `(tau)`.
The open prerequisite concerns one exact `SL_2(Z)` representation, and
the modulus it needs is arbitrary.

The prerequisite is also necessary, since `A_+ <= D`. So this route cannot be
invalidated by a counterexample to the question without that counterexample
also refuting the prerequisite. Its value is that it shrinks the object a
proof or a counterexample must control.
