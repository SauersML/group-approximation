---
rg: 2
id: non-rf-hyperbolic-from-nonsofic-hyperbolic
kind: route
title: A non-sofic hyperbolic group is already not residually finite
target: non-residually-finite-hyperbolic-group
requires:
  - nonsofic-hyperbolic-group
artifacts:
  - research/artifacts/hyperbolic-residual-finiteness-audit-2026-08-17.md
---

Residually finite groups are sofic: the finite quotients `G → F_i` separating
points give exact finite models — homomorphisms into `Sym(F_i)` by left
translation — and a homomorphism is in particular a sofic approximation, with
zero defect and with `1` moved off itself with probability `1 - 1/|F_i|` once
the quotient is large enough to separate the finitely many prescribed
elements.  Contrapositively, a non-sofic group is not residually finite.

So any group witnessing `nonsofic-hyperbolic-group` witnesses this claim too,
and no further work is needed.

**The traffic runs one way.**  The converse implication is false in general
and false in this repository specifically: `E`, the literal finitely presented
group, is sofic (`literal-group-sofic`) and has a nontrivial finite residual
(`literal-mark-quotient-finite-residual`).  So this route is a genuine
reduction of the weaker claim to the stronger one, not a restatement, and the
other three live routes to `non-residually-finite-hyperbolic-group` reach it
without touching soficity at all.

The reason to record it is that it fixes the direction of a confusion the
graph already carried: `nonsofic-hyperbolic-group` describes itself as
"equivalently" answering the residual finiteness question, and equivalence is
exactly what does not hold.
