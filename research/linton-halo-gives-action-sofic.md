---
rg: 2
id: linton-halo-gives-action-sofic
kind: route
title: Lift the free site action through the Linton halo
target: linton-radical-free-action-sofic
requires: [linton-radical-has-equivariant-sofic-halo]
---

Free groups are LERF by Hall's theorem.  Alekseev--Bradford,
*Sofic actions, halo products, and metric approximations of groups*,
arXiv:2601.18742v1, Theorem 4.7, prove that every action of a LERF group on a
set is an LEF action.  Their Proposition 4.20 turns an LEF set action into a
sofic set action.

Apply this to the action `F0` on the site set `X` supplied by the
prerequisite.  Alekseev--Bradford Proposition 4.26 then says that a sofic
action on `X` induces a sofic `C`-action by automorphisms on `L(X)` whenever
all finite halo pieces `L(Y)` belong to `C`.  Take `C` to be the class of
sofic groups.  The prerequisite supplies exactly `L(Y) in C` for every finite
`Y`, so the induced action

```text
F0 -> Aut(L(X))
```

is a sofic action by automorphisms in their Definition 4.23.  Conjugating this
action by the equivariant isomorphism `theta : L(X) -> R` gives precisely
`alpha : F0 -> Aut(R)`.  Sofic automorphic approximation is invariant under
such a conjugacy: transport each finite test set through `theta` and compose
the partial homomorphisms with `theta^{-1}`.  Therefore `alpha` is sofic.

This uses the group law on every `L(Y)` and so does not make the invalid
inference from a merely sofic action on the conjugacy set.  The halo
functoriality is exactly the missing bridge identified in
[[linton-radical-free-action-sofic]].

