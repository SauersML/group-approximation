---
rg: 2
id: mastel-slofstra-generic-bcs-on-lin-loop-proof
kind: route
title: Apply the unconditional one-hot and losing-pair BCS construction to Lin's loop game
target: lin-explicit-fixed-bcs-gap-via-generic-conversion
requires:
  - lin-explicit-synchronous-bell-gap-game
artifacts:
  - research/artifacts/lin-ji-mastel-slofstra-bcs-lcs-boundary-2026-08-23.md
---

Immediately before introducing oracularization in Section 3,
Mastel--Slofstra recall the generic construction with variables `x_(i,a)`,
one-answer constraints, and one constraint `x_(i,a) and x_(j,b)=false` for
each losing answer pair.  They state perfect-strategy equivalence separately
for the quantum, quantum-approximable, and commuting models.  They also state
that the quantum soundness loss is exponential in the answer length.

Apply it to the effective finite `G_loop` supplied by
`lin-explicit-synchronous-bell-gap-game`.  Perfect commuting equivalence
transports Lin's value-one model.  The original loss is at least `1/2`, and
division by a finite, effectively known answer-size factor remains positive;
this gives `delta_loop>0`.  Exponential blowup affects uniform protocol
efficiency, not existence or effectivity of this single finite BCS.
