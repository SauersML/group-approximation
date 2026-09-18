---
rg: 2
id: steinberg-leavitt-resolvent-groups-have-no-type-a-action
kind: claim
title: For N >= 5 the finitely presented group St_N(R_L), which contains every GL_n(Q), has no faithful action with finitely many orbits of pairs, so it is not itself a type (A) actor
distinct_from:
  faithful-pair-finite-steinberg-actions-need-noncentral-k2: that is the unconditional implication from centrality of K_2; this is the flat verdict for R_L, which also needs that centrality.
  gl-n-q-in-permutational-boone-higman-class: that asks for some type (A) actor containing GL_n(Q); this excludes one candidate actor, the Steinberg answer to Problem 2.7.
  type-a-actors-have-no-infinite-virtually-central-subgroup: that is the general necessary condition on actors; this is its application to one named finitely presented overgroup of GL_n(Q).
---

**ESTABLISHED** through route `st-n-r-l-no-type-a-action-via-centre`. Its centrality input
`k2-central-in-steinberg-groups-of-leavitt-resolvent-ring` now rests on
`leavitt-resolvent-k2-stability-holds`, a lane proof by gq-infinite-primes that has not been
independently reviewed. It became established on 2026-09-18.

**Statement.** Let `N >= 5` and `Γ = St_N(R_L)`. Then no action of `Γ` on a set
with finitely many orbits of two-element subsets is faithful. In particular `Γ`
carries no action of type (A), and cannot itself be the actor for
`gl-n-q-in-permutational-boone-higman-class`.

## What the verdict covers

It answers the question of `research/artifacts/gq-gq-critic-2.md`, item (a):
whether there is a faithful action of `Γ` with finitely many orbits of pairs and
finitely generated point stabilizers. The answer does not depend on the
stabilizers.
- **Cosets.** On `Γ/H` with finitely many pair orbits, `H` contains a
  finite-index subgroup of `Z(Γ)`. That subgroup is central, so it lies in the
  core of `H`. So choosing `H` with `H ∩ K_2(N,R_L) = 1` fails.
- **Unconditional part.** A faithful action of `Γ` with finitely many orbits of
  pairs would force `K_2(N,R_L)` to be non-central in `Γ`
  (`faithful-pair-finite-steinberg-actions-need-noncentral-k2`).

## Non-faithful actions and the kernel gate

Assume the centrality claim. Let `Γ` act with type `[A_2]` and kernel `M`.
- **`M` central.** Then `M` has finite index in `Z(Γ)`, and `Γ/M` is not finitely
  presented (item 4 of the implication node). By
  `abstract-btb-simple-quotient-fp-gate` the simple quotient of `SV_Γ` is then
  not finitely presented either.
- **`M` not central.** Then `π(M)` is a non-central normal subgroup of
  `E_N(R_L)`. Suppose every non-central normal subgroup of `E_N(R_L)` is all of
  `E_N(R_L)`, as the sandwich classification gives for commutative rings and
  under stable-range hypotheses; this is not known here for `R_L`. Then
  `M·K_2(N,R_L) = Γ`. So `Γ/M` is abelian, and it is also perfect, hence trivial.
- **Conclusion.** Under both inputs, every action of `Γ` with finitely many pair
  orbits is trivial or has a faithful image that is not finitely presented. So
  `Γ` yields no type (A) actor through its own actions, faithful or not.

## Scope

This excludes `Γ` as the actor, not as an input. `Γ` can still embed in a
different finitely presented type (A) actor. In such an actor its central
elements of infinite order must have infinitely many conjugates
(`type-a-actors-have-no-infinite-virtually-central-subgroup`, corollary 2).

## Attempts

None beyond the route.
