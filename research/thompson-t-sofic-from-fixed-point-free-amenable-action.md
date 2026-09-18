---
rg: 2
id: thompson-t-sofic-from-fixed-point-free-amenable-action
kind: route
title: An invariant mean on a T-set without global fixed points is mean-free by character rigidity, and mean-free amenable actions give sofic approximations
target: thompson-t-is-sofic
requires:
  - thompson-t-has-a-fixed-point-free-amenable-action
  - thompson-t-amenable-actions-are-free-off-fixed-points
---

Let `Ω` be a `T`-set without global fixed points carrying an invariant mean `m`. This is
`thompson-t-has-a-fixed-point-free-amenable-action`. By item 2 of
`thompson-t-amenable-actions-are-free-off-fixed-points`, direction (a ⇒ b), `m` is mean-free, and
by the same item `T` is sofic. The soficity step is item 3 of
`mean-free-amenable-actions-residually-amenable-and-sofic`.

Alternative without characters: as in `thompson-v-sofic-from-fixed-point-free-amenable-action`,
some generator moves positive mass, so the Elek--Szabó obstruction subgroup `N_T` is proper. It is
normal, hence trivial by simplicity, and Proposition 5.1(3) gives soficity.
