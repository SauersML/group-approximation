---
rg: 2
id: amenable-carrier-windows-are-character-transparent-proof
kind: route
title: Amenable coset wreaths plus component averaging build the local countermodels
target: amenable-carrier-windows-are-character-transparent
requires: [heisenberg-solenoid-trace-torsion-dichotomy]
artifacts:
  - research/artifacts/noncommutative-solenoid-unique-trace-memo-2026-08-22.md
---

Window `E_A -> W_A`: send `A` to the base copy and `t` to the lamp at the
base coset (the lamp commutes with the stabilizer `A cap Lambda`, so the
HNN relation maps to a true relation; surjectivity because the lamps are the
`A`-translates).  For amenable `A`, `W_A` is amenable, so EVERY trace of
`W_A` has hyperfinite GNS; pull back `delta_e^(W_A)` and decompose into
extremal components (pullbacks of extremal components — kernel elements act
trivially in GNS — so factorial, and hyperfinite a.e.).  For `A = N`:
components restrict to `N` as a.e. CANONICAL aperiodic traces, because the
component central measures average to Haar and torsion mass integrates to
`Haar(T_p) = 0` (torsion-dichotomy input).  Failure of letter-centrality on
a positive-measure set: for `n = a(1/p)`, the word `t^-1 n^-1 t n` maps to a
product of two distinct lamps, so the average of `Re sigma_x` over
components is 0 while each is `<= 1`; Markov gives measure `>= 1/4` where
`Re <= 1/2`.  Intersect with the co-null canonical set.  Full details and
the elliptic/p-divisibility lemma: THE MEMO, Sections B.2 and B.4.
