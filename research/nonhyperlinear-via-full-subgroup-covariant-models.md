---
rg: 2
id: nonhyperlinear-via-full-subgroup-covariant-models
kind: route
title: A Boolean-full dense subgroup of a non-CE relation's full group with no CE covariant model, plus CE covariant models for hyperlinear actions, gives a non-hyperlinear group
target: non-hyperlinear-group
requires:
  - dense-full-subgroup-without-ce-covariant-model
  - hyperlinear-group-actions-have-ce-covariant-models
---

**Dictionary (entropy-measure family, measure full groups).** This route imports the measure-full-group tools of
orbit equivalence, namely cost, Le Maître's dense free subgroups and full-group cut and paste. Their translations
into character and Connes-embedding language are recorded in `ce-relation-full-group-subgroups-are-hyperlinear`
(table), `dense-full-group-subgroups-generate-relation-factor`,
`nonce-relation-full-groups-contain-dense-free-subgroups` and `support-covariant-models-carry-fixed-point-trace`.
All four are established.

**Route.**
- Q2 = `dense-full-subgroup-without-ce-covariant-model` gives a countable `B`-full dense
  `Gamma_0 <= [R]` whose action on `L^infinity(X)` has no covariant model in a CE algebra.
- `Gamma_0` is a countable group acting on the measure algebra of `(X, mu)` by measure-preserving automorphisms.
- If `Gamma_0` were hyperlinear, Q1 = `hyperlinear-group-actions-have-ce-covariant-models` would give a CE covariant
  model of exactly this action, which is a contradiction.
- Hence `Gamma_0` is a countable non-hyperlinear group.

The group is explicit to the extent that `R` (a property-(T) envelope with an explicit graphing) and the countable
closing-off choices are.

**Why the two prerequisites fail independently.**
- **Q1 alone** is a permanence statement about hyperlinear groups. It says nothing about any particular group, and
  it holds for amenable and free groups. It fails exactly when some hyperlinear group has a measure action with only
  non-CE covariant models. That failure does not touch Q2.
- **Q2 alone** is an obstruction for one action. It fails if, for example, `L^infinity(X) ⋊ Gamma_0` is CE for
  every admissible `(R, B, Gamma_0)`. That failure does not touch Q1. Without Q1, Q2 gives only a non-CE action, not
  a non-hyperlinear group.

**Fences recorded along the way.**
- `nonce-relation-full-groups-contain-dense-free-subgroups` kills every argument that deduces non-hyperlinearity from
  the pair (uniform closure, fixed-point GNS algebra). Density and non-CE of `L(R)` are compatible with `F_3`.
- The naive version of Q2 for dense non-full subgroups is false (Attempts in Q2).
- The support-correction mechanism for Q2 breaks at irreducibility of local covariant algebras. The crossed product
  is the counterexample.

This route does not solve the root. Both prerequisites are OPEN.
