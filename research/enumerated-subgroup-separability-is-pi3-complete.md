---
rg: 2
id: enumerated-subgroup-separability-is-pi3-complete
kind: claim
title: Separability of a recursively enumerated subgroup of the free group of rank two is Pi-zero-three complete, while finitely generated subgroups are always separable
artifacts:
  - research/artifacts/second-level-rice-theorem-2026-08-26.md
distinct_from:
  index-set-profinitely-closed-is-pi3-complete: that classifies closedness of index sets in the profinite topology of the integers; this classifies separability of subgroups of a free group, and its hardness consumes that theorem together with the closure computation for conjugate-basis subgroups.
  centralizing-hnn-is-residually-finite-iff-edge-is-separable: that converts separability into residual finiteness of a group; this is about separability itself, as a decision problem over enumerated subgroups.
  residual-finiteness-two-generator-recursive-is-pi3-complete: that is the group-recognition theorem; this is the subgroup-recognition theorem inside one fixed free group, and it needs no group construction at all.
---

ESTABLISHED.  Code a recursively enumerated subgroup of `F = F(a, b)` by a
program enumerating a set of words; write `S_e` for the subgroup generated
by the words enumerated by `e`.  Then

```text
{ e : S_e is closed in the profinite topology of F }   is Pi^0_3-complete.  (SP1)
```

By contrast, every **finitely generated** subgroup of a free group is
separable (M. Hall), so the same question for subgroups given by a finite
generating tuple is trivially decidable.  The jump from decidable to
`Pi^0_3`-complete happens exactly at the passage from finite generating
tuples to enumerated ones.

**Upper bound.**  `S` is separable iff for every word `k`, either `k in S`
(`Sigma^0_1`) or some finite-index subgroup `U` of `F` contains `S` and
misses `k`.  A finite-index subgroup is presented by a transitive
permutation representation on finitely many points with a base point;
membership in `U` is then decidable, `S <= U` is `Pi^0_1` (check every
enumerated generator), and `k notin U` is decidable.  So the second
disjunct is `Sigma^0_2` and the whole statement is `Pi^0_3`.

**Hardness.**  With `a_j = b^j a b^{-j}` and `A_J = <a_j : j in J>`, the
profinite closure of `A_J` in `F` is `A_{cl(J)}`
([[centralizing-hnn-over-conjugate-basis-is-rf-iff-index-set-closed]]), so
`A_J` is separable iff `J` is closed in the profinite topology of `Z`,
which is `Pi^0_3`-complete by
[[index-set-profinitely-closed-is-pi3-complete]]; the enumeration of the
generators of `A_{J_e}` is computable from `e`.
