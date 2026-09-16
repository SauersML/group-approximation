---
rg: 2
id: hard-type-a-actors-from-hard-fp-self-similar-groups
kind: route
title: Put a hard finitely presented self-similar group inside a type (A) actor by the self-similar permutational theorem and transfer hardness upward
target: type-a-actors-with-arbitrarily-hard-word-problem
requires: [fp-self-similar-groups-with-arbitrarily-hard-word-problem, fp-self-similar-subgroups-satisfy-permutational-boone-higman]
artifacts:
  - research/artifacts/fp-self-similar-hard-wp-swarm-2026-09-16.md
---

## The argument

- **The bound.** Fix a recursive `T` and put `T+(m) = m + max_(k<=m) T(k)`. This
  function is recursive, monotone and at least `T`.
- **A hard self-similar group.** `fp-self-similar-groups-with-arbitrarily-hard-word-problem`
  gives a finitely presented self-similar group `H` whose word problem lies outside
  `F(T+)`.
- **An actor containing it.** By (a) of
  `fp-self-similar-subgroups-satisfy-permutational-boone-higman`, `H` lies in
  `B_A`. So `H <= G` for some group `G` with an action of type (A). By the
  definition in `type-a-action-gives-boone-higman-for-subgroups`, `G` is finitely
  presented and the action is faithful.
- **Transfer.** Write the generators of `H` as words of length at most `L` over a
  finite generating set of `G`. Suppose the word problem of `G` were in `F(T)`.
  The substitution in `complexity-bounded-host-classes-are-not-universal-proof`
  would then give an algorithm for the word problem of `H` in `F(T+)`, a
  contradiction. The embedding need not be effective; `L` is a constant.

So `G` is a finitely presented group with a faithful type (A) action whose word
problem beats `T`. `∎`

## Remarks

- `type-a-actors-with-arbitrarily-hard-word-problem` says in its `distinct_from`
  that neither claim is known to imply the other. This route proves one direction:
  the self-similar claim implies the type (A) claim. By (d) of
  `twisted-brin-thompson-wp-equals-actor-orbit-problem`, it also implies the
  equivalent twisted Brin--Thompson forms. No converse is known, because a type (A)
  actor need not be self-similar.
- The mechanism is the one in `hard-type-a-actors-from-permutational-boone-higman`.
  There the permutational conjecture is assumed for all decidable inputs. Here one
  hard self-similar input per bound is enough, because the self-similar case of the
  permutational property is already established.
