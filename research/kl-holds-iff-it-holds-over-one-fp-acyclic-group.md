---
rg: 2
id: kl-holds-iff-it-holds-over-one-fp-acyclic-group
kind: claim
title: The Kervaire--Laudenbach conjecture holds for all groups iff it holds over one fixed finitely presented acyclic group
distinct_from:
  kervaire-laudenbach-nonsingular-conjecture: that quantifies over all coefficient groups; this is the equivalent single-group form, over the universal finitely presented acyclic group of Palmer--Wu.
  kl-holds-over-two-generator-simple-groups: that restricts to a class of simple coefficient groups; this restricts to one specific finitely presented acyclic group, which is not simple.
artifacts:
  - research/artifacts/hl-kl-minimal-counterexample-2026-09-14.md
---

Let `U_ac` be the finitely presented acyclic group of
`universal-fp-acyclic-group-exists`, which contains every recursively
presented group. Then `kervaire-laudenbach-nonsingular-conjecture` holds if and
only if every nonsingular one-variable equation over `U_ac` injects `U_ac`.
The same holds degree by degree.

## What it does not give

A finite search. `U_ac` has unsolvable word problem, so "a coefficient dies"
is r.e. over `U_ac` but "it is nontrivial" is not. Higman's universal finitely
presented group gives the same equivalence without acyclicity.

DERIVATION
kl-single-fp-acyclic-host-proof
