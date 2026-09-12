---
rg: 2
id: alternating-lamp-noncommensurable-family
kind: claim
title: An infinite noncommensurable family sharing one visible approximation theory
distinct_from:
  continuum-nonisomorphic-fg-non-mf: That is a cardinality statement separating isomorphism types of non-MF groups by external direct factors `E x N_i`; this family is countable, is separated by the much stronger relation of noncommensurability, and its members are pairwise indistinguishable by every finite, profinite, compact, linear, and corona target.
  scaling-family-pairwise-nonisomorphic: That asks to separate the explicit scaling family `E_m`, all built by the same construction at different scales, and separation there is by isomorphism type; this separates alternating-lamp wreath groups up to commensurability using the simple type stored in the radical.
  profinite-twins-opposite-mf: That is a two-group statement pairing one non-MF group with one MF group; this is an infinite family of mutually non-MF groups, all sharing the single MF quotient of that pair.
  simple-lamp-radical-one-relation: That measures the presentation-theoretic size of a single member's hidden kernel; this compares different members of the family to each other.
artifacts:
  - GroupApproximation/Algebra/AlternatingLampNoncommensurable.lean
  - research/artifacts/multi-mover-hnn-dossier-2026-08-15.md
  - GroupApproximation/Algebra/PermutationalWreathSimple.lean
---

For `n >= 5` put

    W_n = A_n^(G*/Gamma*) x| G*.

Every `W_n` is finitely generated, sofic, hyperlinear, and not MF, with
`Rad_MF(W_n) = A_n^(G*/Gamma*)` and visible quotient `G*` independent of `n`.

The family is **pairwise noncommensurable**: for `m != n`, no finite-index
subgroup of `W_m` is isomorphic to a finite-index subgroup of `W_n`.  In
particular the members are pairwise non-isomorphic.

Yet all of them share, through the same quotient `G*`:

- the same profinite completion and the same Bohr compactification;
- corresponding finite-index subgroup lattices with equal indices, hence the
  same subgroup growth;
- the same category of finite actions;
- the same finite-dimensional representation categories over every field;
- the same Hom-sets into every norm matrix corona.

The distinguishing datum — which alternating group is being used — lives
entirely inside a fully invariant subgroup that every one of those theories
erases.
