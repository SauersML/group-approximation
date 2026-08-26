---
rg: 2
id: shift-raag-family-is-rf-iff-symmetrized-index-set-closed
kind: claim
title: The two-generator group in which a commutes with its prescribed t-conjugates is residually finite iff the symmetrized index set is profinitely closed
distinct_from:
  shift-raag-family-classifies-amenability: that decides amenability of the same family by completeness of the shift graph; this decides residual finiteness by profinite closedness of the index set, so the same two-generator family carries both switches.
  centralizing-hnn-over-conjugate-basis-is-rf-iff-index-set-closed: that criterion is for the three-generator centralizing family, where the closure acts on a free factor of a normal subgroup of the base; this is the two-generator family, where the closure acts on non-edges of the shift graph and the separating quotients are right-angled Artin groups of finite cyclic graphs.
---

ESTABLISHED.  For `J <= Z_{>0}` let `G_J = < a, t | [a, t^j a t^-j] = 1, j in J >`
be the group of [[shift-raag-family-classifies-amenability]], and put
`J^s = J u (-J) u {0}`.  Then

```text
G_J is residually finite   iff   J^s is closed in the profinite topology of Z.   (SF1)
```

Equivalently: iff for every `d notin J^s` there is `m >= 1` with
`(d + mZ) n J^s` empty.

The separating quotients are `A(Gamma_{J,m}) x| Z/m`, where
`Gamma_{J,m}` is the graph on `Z/m` with `u -- v` iff `v - u in J mod m`;
the obstruction, when `d in cl(J^s) \ J^s`, is the commutator
`[a, t^d a t^-d]`, nontrivial by the right-angled Artin structure but dead
in every finite quotient because a finite-order image of `t` folds `d`
onto a prescribed index.

This is the two-generator counterpart of
[[centralizing-hnn-over-conjugate-basis-is-rf-iff-index-set-closed]] and
feeds [[residual-finiteness-two-generator-recursive-is-pi3-complete]].
