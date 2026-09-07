---
rg: 2
id: universal-finite-obstruction-proof
kind: route
title: Cover the seed group along its signed swap
target: universal-finite-obstruction-order-four
requires:
  - torsion-normal-generator-fp-cover-linear-gap
  - universal-seed-marked-generation-bound-sixteen
artifacts:
  - research/artifacts/universal-seed-review-2026-09-07.md
---

## Why sufficient

Take `G = B = EL_4(C)` and `a` its signed swap.  `B` is finitely generated,
`Res_MF(B) = B`, and `a` normally generates `B` with `a^4 = 1` and order
exactly four, all from
`universal-seed-marked-generation-bound-sixteen` and the nodes it consumes.

Apply `torsion-normal-generator-fp-cover-linear-gap` with `m = 4`.  It
returns `P`, `alpha` and `C_0` with clauses 1 and 2, together with a
surjection `pi : P ->> B` sending `alpha` to `a`.

For clause 3, compose `pi` with the homomorphism `f : B -> EL_n(R')` of the
marked-generation node.  Then `alpha` maps to `f(a)`, which normally
generates `EL_n(R')`, and clause 4 is that node's bound verbatim.
