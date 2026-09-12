---
rg: 2
id: boone-higman-via-ck-quotient-cosets
kind: route
title: Excluded repair by a finitely presented quotient with finite canonical-core bi-index
target: boone-higman-conjecture
requires: [boone-higman-thompson-simple-envelope, chatterji-kassabov-normal-generator-embedding, universal-sandwich-ring-is-finitely-presented-and-injective, ck-quotient-coset-repair, simple-core-bi-index-counts-coset-action-pair-orbits, twisted-brin-thompson-finite-presentation-criterion]
artifacts:
  - research/artifacts/ck-quotient-and-cover-bi-index-obstruction-2026-09-08.md
---

The implication records the previously proposed quotient repair. Its
quotient-existence premise is now refuted, so this is not a live route.

Given a finitely generated word-problem group, first embed it in an
infinite finitely generated computably presented simple group `S`. Use
the universal-sandwich construction to put `S` in its normal-generator
elementary envelope `Gamma` as the corner subgroup `D`.

If the asserted quotient `Q=Gamma/N` existed, every nontrivial corner
element would still normally generate `Q`, and the corner copy would
remain isomorphic to `S`. The latter follows either from simplicity and
normal generation or from the root-kernel calculation in the artifact.
If `q(D)=Q`, the finitely presented group `Q` would already be the
desired simple envelope. Otherwise the coset-action lemma makes the
action on `Q/q(D)` faithful. Its stabilizers would be finitely generated,
and finite bi-index would give finitely many pair-orbits. The twisted
Brin–Thompson criterion would then supply a finitely presented simple
overgroup of `Q`, completing Boone–Higman.

The new obstruction refutes precisely the finite-bi-index quotient
premise. It does not refute the route that instead asks directly for a
finitely presented simple quotient.
