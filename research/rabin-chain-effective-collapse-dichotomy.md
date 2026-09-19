---
rg: 2
id: rabin-chain-effective-collapse-dichotomy
kind: claim
title: Rabin's chain, effectively - a computable presentation map with the collapse dichotomy
distinct_from:
  adian-rabin-transform-for-mf: That is the finished datum for this repository's forbidden group E, and additionally needs a finitely presented source group with undecidable word problem; this is the construction itself, uniform in the forbidden group and with no undecidability in it.
  torsion-free-higman-embedding: That is an embedding theorem for recursively presented groups; this is a computable chain of HNN extensions and free products with a triviality-versus-containment conclusion, and Higman embedding is what it must avoid needing.
artifacts:
  - GroupApproximation/Computability/AdianRabinMarkovProperty.lean
---

OPEN.  Item **D5** of the cost table in [[adian-rabin-transform-for-mf]],
1500--3000 lines.  Given a finitely presented group `H` with a distinguished
word `w`, and a finitely presented forbidden group `F`, a computable map on
presentations producing `P_w` with

* `G(P_w)` trivial when `w = 1` in `H`, and
* `F` embedding in `G(P_w)` when `w != 1` in `H`.

Rabin's chain of HNN extensions and free products, with the collapse-to-trivial
induction.

## Why it is worth a node of its own

It carries no computability hypothesis and no MF: it is a group-theoretic
construction plus the observation that each step is computable on
presentations.  Separating it from [[adian-rabin-transform-for-mf]] is what
makes the remaining frontier legible -- the transform needs *both* an
undecidable source group and this construction, and only the first of the two
has any prospect of arriving as a by-product of other work.

It is also uniform in `F`.  Specializing to this repository's `E` removes no
step, which is the first of the four recorded non-shortcuts in the consumer.
