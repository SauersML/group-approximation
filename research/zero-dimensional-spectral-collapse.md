---
rg: 2
id: zero-dimensional-spectral-collapse
kind: claim
title: Zero-dimensional-spectrum witnesses collapse under one-sided Kazhdan compression
distinct_from:
  compression-torsion-collapse: That claim needs the witness to have finite image order; this one needs only zero-dimensional spectrum of the represented unitary, covering Cantor spectra, and derives the finite-order case by spectral projections rather than by a separate rank-cocycle argument.
  semisimple-packet-multiplicity-collapse: That open claim concerns noncommutative finite-dimensional packets, where joint spectral projections do not exist; this one is the commutative case, where they do, and it is established.
---

Let `E` be countable, `L <= E` with property (T), `s L s^{-1} <= L`, and
`pi : E -> U(Q)` a corona representation.  Let `v in Q` be a unitary with

1. `[v, pi(s L s^{-1})] = 0`;
2. pairwise commuting `L`-conjugates `pi(gamma) v pi(gamma)^*`;
3. `sigma(v)` zero-dimensional.

Then `[v, pi(L)] = 0`.

**Consequences.**  Every finite-spectrum witness collapses; every
finite-order witness collapses (`v^m = 1` gives `sigma(v) <= mu_m`); the
separate finite-`m` analytic program is conceptually closed by spectral
projection reduction from the involutive case.  Torsion abelian lamps over
a compressed Kazhdan site space therefore always obstruct MF, which is the
negative half of `abelian-lamp-mf-classification`.
