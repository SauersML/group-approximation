---
rg: 2
id: char-two-leavitt-path-unit-groups-satisfy-pbh
kind: claim
title: Unit groups of Leavitt path algebras of countable graphs with finitely many vertices, over finite fields of characteristic two, satisfy permutational Boone--Higman
distinct_from:
  binary-leavitt-unit-group-satisfies-pbh: that is the one-vertex, two-loop algebra over F_2; this is every countable graph with finitely many vertices over every finite field of characteristic two, obtained by embedding in that group.
  leavitt-unit-groups-over-finite-fields-mutually-embed: that gives mutual embeddings of the one-vertex unit groups within one characteristic; this adds the multi-vertex graphs and draws the permutational conclusion.
  char-two-curve-linear-groups-satisfy-permutational-boone-higman: that is the class of characteristic-two linear inputs placed in the binary unit group; this is the class of Leavitt path unit groups placed in it.
artifacts:
  - research/artifacts/leavitt-pbh-general-2026-09-13.md
---

**ESTABLISHED (2026-09-13)** through `char-two-leavitt-path-pbh-via-binary-embedding`. Not
independently reviewed. No novelty is claimed for the algebra embeddings, which are
imported or already on main.

## Statement

Let `F` be a finite field of characteristic two and `E` a countable directed graph with
finitely many vertices, for instance any finite graph. Then `L_F(E)^x`, and every subgroup of
it, embeds in a finitely presented group admitting an action of type (A). In particular
this holds for every `L_(F_(2^k))(1,n)^x` with `n >= 2`.

## Consequences

- **BFFHZ Question 3.4, one group at a time.** Let `S` be a finitely presented simple group
  that embeds in some such `L_F(E)^x`. Then `S` is finitely generated with solvable word
  problem and lies in `B_A`. By BFFHZ Theorem C, (i) ⟹ (iv)
  (`fp-simple-highly-transitive-groups-satisfy-pbh`), `S` embeds in a finitely presented
  simple MIF group, so `S` answers `fp-simple-groups-embed-in-fp-simple-mif-groups`
  positively. The instance on main is `L_(F_2)(1,2)^x` itself, which is finitely presented
  (`leavitt-unit-group-finitely-presented`) and simple (`binary-leavitt-unit-group-is-simple`).
- **Not every member is simple.** By `leavitt-unit-max-mf-quotient-is-power-cokernel`, the
  unit group of `L_(F_q)(1,n)` has the abelian quotient `C_(gcd(q-1, n-1))`, which is
  nontrivial for example for `q = 4`, `n = 4`. Which of these unit groups, or their
  commutator subgroups, are finitely presented and simple is not settled here.

## Scope

Only finite fields of characteristic two are covered, because the field-lowering step of
`leavitt-unit-groups-over-finite-fields-mutually-embed` needs a finite-dimensional regular
representation over `F_2`. Odd characteristic is the OPEN node
`prime-field-leavitt-unit-groups-satisfy-pbh`.
