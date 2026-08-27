---
rg: 2
id: sl3-codense-coset-lamp-recursive-host-proof
kind: route
title: Turn finite-quotient codensity into transitivity of every finite-orbit coloring core
target: sl3-codense-coset-lamp-recursive-host
requires:
  - recursive-permutational-lamp-presentation
  - infinite-character-actor-kills-fd-mark
  - exact-projective-codensity-has-a-uniform-trace-square-gap
---

Let a finite character orbit have core `N normal A`.  The quotient map
`A->A/N` has the same image on `C`, so `A=CN`.  Consequently `N` is
transitive on `A/C`; any `N`-fixed coloring is constant and is trivial on
the two-point seed.  The infinite-character criterion kills `J` in every
exact finite-dimensional representation and keeps it in the translation
model.  The recursive lamp presentation applies because `A` is finitely
presented and membership proofs in the finitely generated subgroup `C` are
recursively enumerable.
