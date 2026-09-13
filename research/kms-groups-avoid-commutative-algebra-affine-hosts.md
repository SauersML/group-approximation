---
rg: 2
id: kms-groups-avoid-commutative-algebra-affine-hosts
kind: claim
title: Some finitely presented residually finite group in A_p^2 A embeds in no affine group of a module over a finitely generated commutative algebra over a finite field
distinct_from:
  uniform-wp-bound-excludes-bh-universal-targets: that excludes a solvable class-three input from an arbitrary bounded class; this names the bounded class (affine groups over commutative algebras of positive characteristic) and takes the excluded input in the variety A_p^2 A.
  kms-natural-affine-actor-has-infinitely-many-orbits: that shows the group's own affine action on its configuration module is not of type (A); this excludes every embedding into an affine group over a commutative algebra of positive characteristic, whatever the action.
  kms-configuration-letters-avoid-finite-orbit-placements: that excludes finite-orbit placements of the configuration letters by a module argument; this excludes translation placements over commutative algebras by a complexity argument.
artifacts:
  - research/artifacts/solve-kms-self-similar-affine-2026-09-13.md
---

**ESTABLISHED** by `kms-commutative-affine-host-exclusion-proof`. Not independently
reviewed; no novelty is claimed.

## Statement

There are a prime `p` and a finitely presented residually finite group `G` in
`A_p^2 A`, one of the Kharlampovich--Myasnikov--Sapir Minsky-machine groups, such
that `G` embeds in no group `Aff_R(S) = S x| Aut_R(S)`, where `R` is any finitely
generated commutative algebra over a finite field and `S` any finitely generated
`R`-module.

In particular `G` embeds in no `GL_n(R)` over such an `R`. It also embeds in none of
the finitely presented self-similar affine hosts `R^N x| E_N(R)`,
`R = F_p[s_1, ..., s_k]`, used by
`char-p-linear-groups-satisfy-permutational-boone-higman`.

## Meaning for `fp-rf-apapa-groups-satisfy-boone-higman`

- **What is closed.** The lamps artifact named "translations over a ring (as in the
  F_p[s] self-similar hosts)" as a surviving placement. For the hard members of the
  class, translations over commutative algebras of positive characteristic are dead,
  as are all hosts over them.
- **Why.** The obstruction is complexity, not module structure.
  `<x(q_j), a_1, a'_1>` is Baumslag's group, which does sit in such a host. What fails
  is containing the whole machine.
- **What survives.** Hosts whose word problems share no recursive bound:
  - affine or linear groups over non-commutative algebras that carry the Minsky
    semigroup;
  - infinite-state self-similar groups;
  - germ placements beyond the rational class.
  Any of these that is of type (A) settles `type-a-actors-with-arbitrarily-hard-word-problem`.
