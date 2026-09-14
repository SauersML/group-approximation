---
rg: 2
id: kl-counterexample-can-have-solvable-word-problem
kind: claim
title: Any Kervaire--Laudenbach counterexample can be taken with solvable word problem
distinct_from:
  kl-counterexample-can-be-finitely-presented: that is established and yields finite presentation data; this asks in addition for a decidable word problem, which finite presentation does not supply.
  fp-simple-kl-failure-transfers-through-decidable-groups: that is the established transfer between finitely presented simple counterexamples and decidable ones under Boone--Higman; this is the missing existence input on the decidable side.
---

**OPEN.**  If `kervaire-laudenbach-nonsingular-conjecture` fails, it fails over
a finitely generated group with solvable word problem.

## Why it is not free

By `kl-class-is-a-quasivariety` a failure is a template `(P, w, alpha)` with `P`
finitely presented and `alpha != 1` in `P`.  A decidable counterexample needs a
finitely generated group `G` with solvable word problem and a homomorphism
`P -> G` in which `alpha` survives.  Nothing forces such a quotient to exist.
Finitely presented groups can have unsolvable word problem, and passing to a
quotient that keeps `alpha` alive gives no control of decidability.

## Attempts

1. **Residually finite quotients.**  A finitely presented residually finite
   group has solvable word problem (McKinsey's algorithm, not re-read here).
   But a residually finite counterexample is impossible: it is residually
   finite, hence residually hyperlinear, hence in `KL` by
   `kl-class-is-a-quasivariety` item 2 and
   `kervaire-laudenbach-holds-for-hyperlinear`.  Dead as a source.
2. **Simple quotients.**  A finitely presented simple quotient in which `alpha`
   survives has solvable word problem by Kuznetsov.  Producing one is the
   question itself; see `kl-counterexample-can-be-finitely-presented-simple`.
