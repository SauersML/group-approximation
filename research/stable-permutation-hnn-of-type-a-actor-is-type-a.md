---
rg: 2
id: stable-permutation-hnn-of-type-a-actor-is-type-a
kind: claim
title: An HNN extension of a type (A) actor, realized faithfully by one more permutation of the same set with finitely many edge-group orbits, again acts of type (A)
distinct_from:
  type-a-actions-closed-under-products-and-finite-wreaths: that builds actors from finite direct products and finite wreaths; this builds an actor from an HNN extension realized on the actor's own set by one extra permutation, where pair-orbit finiteness is inherited and the stabilizer clause carries the work.
  boone-higman-type-a-class-closed-under-finite-extensions: that is closure of the permutational class under finite direct products and finite-index overgroups; this is closure under HNN extensions that are realized faithfully on the actor's set with finitely many edge-group orbits.
  finite-index-edge-hnn-embeds-in-fp-simple-group: that uses the Bass--Serre tree action and needs finite-index edges and a residually finite vertex group; this uses the actor's own permutation action, allows edges of any index, and puts the difficulty into a faithful realization.
  bh-embeddability-survives-decidable-edge-hnn: that is the open permanence with no realization hypothesis; this proves the permanence for inputs that sit in an actor on which the HNN extension is realized faithfully.
---

**ESTABLISHED.** Let `Gamma` act on `X` of type (A), in the sense of
`type-a-action-gives-boone-higman-for-subgroups`. Let `D_1, D_2 <= Gamma` be
finitely generated, let `psi : D_1 -> D_2` be an isomorphism, and let `pi` be a
permutation of `X` with `pi d pi^-1 = psi(d)` as permutations, for every
`d in D_1`. Let

```text
L = Gamma*_psi = < Gamma, t | t d t^-1 = psi(d), d in D_1 >,
```

and let `rho : L -> Sym(X)` extend the action of `Gamma` by `t -> pi`.

(a) **Type (A).** If `rho` is injective and `D_1` has finitely many orbits on
`X`, then `L` acting on `X` through `rho` is of type (A).

(b) **Envelopes.** Under (a), every subgroup of `L` embeds in a finitely
presented simple group. In particular, if `A <= Gamma`, `C_i = A ∩ D_i` and
`psi(C_1) = C_2`, then `A*_phi` with `phi = psi|_(C_1)` embeds in a finitely
presented simple group.

(c) **Mapping tori.** Suppose `pi` normalizes `rho(Gamma)`, and let `phi` be
conjugation by `pi` on `Gamma`. If no nonzero power of `pi` lies in
`rho(Gamma)`, then `Gamma ⋊_phi Z` acting through `t -> pi` is of type (A). If
some power `pi^n` with `n >= 1` lies in `rho(Gamma)` and `Gamma` has an element of
infinite order, then `Gamma ⋊_phi Z` still embeds in a group with a type (A)
action.

## Where it stops

Finite presentation and pair-orbit finiteness come for free here. Three things
do not:

1. an actor `Gamma` containing the given vertex group must exist, which for that
   group is `permutational-boone-higman-conjecture`;
2. the edge groups must be enlarged inside `Gamma` to `D_i` that meet the vertex
   group exactly in the old edges, have finitely many orbits on `X`, and are
   permutation-isomorphic through `psi`;
3. `rho` must be injective, a Britton-type ping-pong condition on `pi` that
   nothing here supplies except in case (c).

The derivation is `stable-permutation-hnn-of-type-a-actor-is-type-a-proof`.
