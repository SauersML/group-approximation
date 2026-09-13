---
rg: 2
id: binary-leavitt-unit-group-satisfies-pbh
kind: claim
title: The binary Leavitt unit group embeds in a finitely presented group with a type (A) action
distinct_from:
  leavitt-subalgebra-linear-groups-satisfy-boone-higman: that embeds linear groups over subalgebras of the binary Leavitt algebra in the finitely presented simple unit group, which is Boone--Higman for them; this asks for the permutational form for the whole unit group, hence for all of its subgroups.
  permutational-boone-higman-conjecture: that is the universal statement for every decidable group; this is one input, a finitely presented simple nonsofic group.
  decidable-groups-embed-in-orbit-finite-affine-actors: that is the universal affine target; this is one instance, over the Cantor module of the Leavitt algebra.
---

**ESTABLISHED (2026-09-13)** through `leavitt-pbh-via-cantor-module-affine-actor`, once
`leavitt-cantor-module-semidirect-product-is-fp` was established (not independently
reviewed). Let `R = L_(F_2)(1,2)` and `U = R^×`. Then `U` embeds in a finitely
presented group admitting an action of type (A). Equivalently, by
`fp-simple-highly-transitive-groups-satisfy-pbh` (BFFHZ Theorem C), `U` embeds in a
finitely presented simple highly transitive group, or in a finitely presented simple
MIF group.

**Why this input matters.** `U` is finitely presented (`leavitt-unit-group-finitely-presented`)
and simple (`binary-leavitt-unit-group-is-simple`), so every subgroup of `U` already
satisfies Boone--Higman. This claim upgrades all of them to the permutational form, which
is stable under commensurability, direct products and free products (BFFHZ Corollary F).
It puts `U`, the group of the Leavitt route `fp-simple-nonsofic-via-leavitt-unit-group`
into `fp-simple-nonsofic-group`, in the class `B_A`. The type (A) action is that of
`C(C, F_2) ⋊ U` on `C(C, F_2)`. No node on main states that `U` itself is highly
transitive or MIF.

## Routes

- `leavitt-pbh-via-cantor-module-affine-actor`: `U` acts faithfully and linearly on
  the Cantor module `C(C, F_2)` with finitely many orbits, so the affine criterion
  (`orbit-finite-affine-actions-are-type-a`) reduces this claim to finite presentation
  of `C(C, F_2) ⋊ U`. That is `leavitt-cantor-module-semidirect-product-is-fp`,
  established 2026-09-13 through `leavitt-cantor-module-fp-via-thompson-amalgam`. All
  five requirements of the route are established.

## Attempts

1. **Highly transitive or MIF directly.** Not tried here. `U` acts linearly on
   `C(C,F_2) \ {0}`, which is not highly transitive: linear dependence of triples is
   invariant. Thompson's `V <= U` is highly transitive on an orbit of the Cantor set,
   but `U` does not act on the Cantor set. No faithful highly transitive action of `U`
   is known to this graph.
