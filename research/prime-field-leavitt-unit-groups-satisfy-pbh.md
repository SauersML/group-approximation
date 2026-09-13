---
rg: 2
id: prime-field-leavitt-unit-groups-satisfy-pbh
kind: claim
title: For every prime p the unit group of the binary Leavitt algebra over F_p satisfies permutational Boone--Higman
distinct_from:
  binary-leavitt-unit-group-satisfies-pbh: that is the case p = 2; this asks for every prime, where odd p needs a finite presentation and a covered generating set that are not on main.
  char-two-leavitt-path-unit-groups-satisfy-pbh: that covers every Leavitt path unit group over finite fields of characteristic two; this asks for the analogue in odd characteristic, through its one-vertex binary member.
---

**OPEN for odd `p`.** The case `p = 2` is `binary-leavitt-unit-group-satisfies-pbh`.

For a prime `p`, `L_(F_p)(1,2)^x` embeds in a finitely presented group with an action of type
(A).

## Why one group per characteristic suffices

By `countable-graph-leavitt-path-algebras-embed-in-binary-leavitt` and
`leavitt-unit-groups-over-finite-fields-mutually-embed`, every `L_F(E)^x`, for `F` finite of
characteristic `p` and `E` countable with `E^0` finite, embeds in `L_(F_p)(1,2)^x`. Conversely
`L_(F_p)(1,2)^x` is one of them. So this claim for `p` is equivalent to the permutational
property for all of them, exactly as in `char-two-leavitt-path-unit-groups-satisfy-pbh`.

## Routes

- `prime-field-leavitt-pbh-via-covered-module-amalgam`: the Cantor module `C(C, F_p) ⋊ V` is
  finitely presented for every `p` (`higman-thompson-cantor-module-products-are-fp`). The
  amalgamation lemma then needs only a finite presentation of the unit group and a generating
  set of `V` together with elementary and diagonal units. That is the OPEN premise
  `odd-prime-leavitt-unit-groups-are-fp-and-covered`.

## What is known around it

- `K_1(L_(F_p)(1,2)) = F_p^x / (F_p^x)^1 = 1` (`leavitt-unit-max-mf-quotient-is-power-cokernel`).
- For odd `p` the centre of the unit group contains `-1`, so the group is not simple. Several
  nodes on main work with `G_3 = L_(F_3)(1,2)^x` and `z = -1`.
