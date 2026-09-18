---
rg: 2
id: fp-tree-groups-have-computable-faithful-tree-actions
kind: claim
title: A finitely presented group with a faithful action on the d-regular rooted tree has a computable faithful action on that tree, given by one algorithm uniform in the presentation
distinct_from:
  finite-class-kms-groups-act-on-regular-rooted-trees: that builds a faithful regular-tree action for one family by bounding the primes of its finite quotients; this takes any faithful action as given and makes it computable, for every finitely presented group.
  some-fp-rf-group-acts-on-no-regular-rooted-tree: that is the open hole on the existence of a faithful action; this shows that for finitely presented groups existence already gives a computable one, so that hole cannot be split off from a computability condition.
---

**ESTABLISHED** (route
[[fp-tree-groups-have-computable-faithful-tree-actions-proof]]).

Let `d >= 2` and let `T_d` be the rooted tree with vertex set `X^*`,
`X = {0, 1, ..., d-1}`. There is an algorithm that takes a finite presentation
`G = <S | R>` and outputs a Turing machine computing a homomorphism
`tau : G -> Aut(T_d)`, i.e. computing `tau(s)(w)` from `s in S^{+-1}` and
`w in X^*`. The homomorphism `tau` is faithful whenever `G` admits some faithful
homomorphism `G -> Aut(T_d)`.

**Consequence.** Let `G` be finitely presented. If `G` embeds in `Aut(T_d)`,
then `G` has a computable faithful action on `T_d`. Hence `G` has solvable word
problem, and its level quotients are computable.

**Scope.** The input group must be finitely presented, so that homomorphisms to
finite groups can be enumerated. For a recursively presented group, or a
finitely generated group with solvable word problem, the statement is not
claimed.
