---
rg: 2
id: kms-arbitrarily-hard-fp-rf-groups
kind: claim
title: Finitely presented residually finite groups realize arbitrarily hard decidable word problems
distinct_from:
  decidable-fp-groups-need-not-embed-in-rational-group: that is the consequence drawn from this import for one target class, groups of rational Cantor homeomorphisms; this is the imported hardness theorem itself, with no target class in it.
  rational-homeomorphism-subgroups-have-exponential-wp: that is an upper bound on the word problem of one family of groups; this is a lower-bound realization theorem, and the two are combined only in their consequences.
artifacts:
  - research/artifacts/boone-higman-complexity-wall-2026-09-11.md
---

ESTABLISHED by literature import. For every recursive membership problem `X`
there is a finitely presented residually finite group `G`, solvable of class
three, such that

```text
any algorithm deciding the word problem of G in time T
yields an algorithm for X in time C*T(C*n) + C*n + C,        (KMS1)
```

for a constant `C` depending only on `G` and the chosen finite generating set.

Every such `G` has decidable word problem, since a finitely presented
residually finite group does.

`(KMS1)` is a statement about word-problem *time complexity*. A lower bound on
the Dehn function or the depth function would not give it, and the same paper
supplies those separately.

Consequence used downstream: writing

```text
F(g) = { L : L decidable in time C*g(C*n) + C*n + C for some C }   (KMS2)
```

for a recursive non-decreasing `g`, `(KMS1)` says that if `X` is not in
`F(g)` then the word problem of `G` is not in `F(g)` either, because `F(g)`
is closed under the substitution in `(KMS1)`.

DERIVATION
kms-arbitrarily-hard-fp-rf-groups-citation
