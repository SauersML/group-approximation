---
rg: 2
id: groups-with-finite-evc-model-are-virtually-cyclic
kind: claim
title: Every group admitting a finite model for the classifying space for virtually cyclic subgroups is virtually cyclic
distinct_from:
  finite-evc-model-implies-fp-and-bvc: that claim derives finite presentation and BVC from a finite model; this claim derives virtual cyclicity
---

The Juan-Pineda–Leary conjecture (Contemp. Math. 407 (2006), Conjecture 1): if a group `G`
admits a `G`-CW model for `E_VC G` with finitely many orbits of cells, then `G` is
virtually cyclic. This is part (A) of `zaremsky-1-07-juan-pineda-leary-conjecture`.

It follows from `finitely-presented-bvc-groups-are-virtually-cyclic` through
`jpl-conjecture-from-conjecture-b`.

## Attempts

- Known classes: hyperbolic groups (Juan-Pineda–Leary, Corollary 12), elementary amenable
  groups (Kochloukova–Martínez-Pérez–Nucinkis 2011), every class in the known-cases list of
  the root, Artin groups (von Puttkamer–Wu, arXiv:1807.10095), residually finite groups
  (Barnea–Camina–Ershov–Lewis, arXiv:2210.15746, Corollary 8.4(a)). See
  `research/artifacts/zp-jpl-bvc-known-classes-2026-09-13.md`.
- A proof of (A) that uses more than BVC could use the rest of von Puttkamer–Wu 1607.03790,
  Proposition 1.1: `G` has a finite model for `E_FIN G`, Weyl groups of finite subgroups are
  finitely presented and of type `FP_infinity`, and `G` has type `F_infinity`. No such
  argument is known to this lane. Every published proof goes through BVC.
