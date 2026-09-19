---
rg: 2
id: fp-simple-short-expander-profiles-escape-recursive-bounds
kind: claim
title: Some finitely presented simple group has, for some rational δ > 0, short-expander profile X^δ beyond every recursive bound
distinct_from:
  fp-simple-amenable-subgroups-beat-every-recursive-folner-bound: that is statement E about Følner functions of amenable subgroups; this is the host-level gate of the single-host short-expander route to E, about finite subgroups of the host with no amenability.
  torsion-amplifies-to-kazhdan-expanders-over-group-rings: that proves the same growth for EL_3(F_2[2V]), which is not known to lie in a finitely presented simple group; this asks for it in a finitely presented simple group.
  brin-thompson-torsion-orders-escape-every-recursive-bound: that is the weaker finite-subgroup and torsion growth, established for 2V; this asks for expander growth.
---

**OPEN.** There are a finitely presented simple group `P`, a finite generating
set, and a rational `δ > 0` such that `X^δ_P` is not recursively bounded. Here
`X^δ` is the profile of
`finiteness-decidable-iff-finite-subgroup-profile-recursive`.
Equivalently, since `P` has solvable word problem (Kuznetsov; standard, not
read at source here), the δ-expander problem of `P` is undecidable. That is item
3 of the same node.

## Place in the route to E

For a finitely presented simple `P`, write **E_X(P)** for the single-host
short-expander form: for every recursive `U` there is a finitely generated
amenable `H_U <= P` with `X^δ_(H_U) ⋠ U`.

- **E_X(P) implies E.** Apply coset averaging, item 1 of
  `amenable-recursive-groups-have-recursive-expander-profile`, with `U(L^2)` in
  place of `U`.
- **E_X(P) implies this claim for `P`.** Let `X^δ_P <= R` with `R` recursive
  and non-decreasing, and let `c_U` bound the `P`-lengths of generators of
  `H_U`. Item 4 of the profile node gives `X^δ_(H_U)(L) <= R(c_U L)`, so
  `X^δ_(H_U) ≼ R` for every `U`. That fails at `U = R`.
- **This claim implies an undecidable finiteness problem in `P`.** This is items
  2 and 4 of the profile node, with `X^δ <= FS`.
- **E_X(P) needs more than this claim.** The `H_U` must be amenable, and they
  must genuinely vary with `U`, since each single one has recursive `X^δ` by
  item 2 of `amenable-recursive-groups-have-recursive-expander-profile`. They
  must also not form a certified family, by item 4 of
  `folner-separators-of-boone-higman`.

So the single-host route splits into two gates, each able to fail on its own:

- **G1 (host expansion):** this claim.
- **G2 (amenable localization):** the step from host expanders to varying
  amenable subgroups.

## What is known here

- *The necessary finite-subgroup condition holds in `2V`, and in every
  finitely generated group with solvable word problem containing it,* by
  `brin-thompson-torsion-orders-escape-every-recursive-bound`.
- *It fails in the Higman--Thompson groups,* whose `FS` is recursive by
  pumping (w10 lane, not on this branch). So none of them is a `P`.
- *Cyclic and abelian witnesses cannot supply G1,* by
  `abelian-finite-expanders-have-recursively-bounded-order`.
- *A sufficient condition.* If the finitely generated group `EL_3(F_2[2V])`,
  which has solvable word problem, embeds in some finitely presented simple
  group, then this claim holds, by
  `torsion-amplifies-to-kazhdan-expanders-over-group-rings` and item 4.
  The Boone--Higman conjecture predicts that embedding.
- *The direct question for `2V`.* Is the δ-expander problem of `2V` itself
  undecidable? A positive answer would need, from a torsion element `g` of
  large order, short elements of `2V` generating a finite expander of order
  growing with `ord(g)`. The linear model `EL_3(F_2[<g>])` acts linearly, not
  by prefix replacements. Its infinite analogue `EL_3(F_2[t,t^-1])` acts on
  `(F_2^3)^Z` by linear cellular automata, which are not elements of `2V`. No
  such construction is known here.
