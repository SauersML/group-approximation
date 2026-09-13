---
rg: 2
id: universal-fp-group-hosts-have-unsolvable-word-problem
kind: claim
title: "Every group containing a universal finitely presented group has unsolvable word problem, infinite cohomological dimension and finite subgroups of every order"
distinct_from:
  unsolvable-word-problem-does-not-obstruct-type-f-infinity: that says type F_infinity is compatible with an unsolvable word problem (Collins--Miller), so word-problem complexity cannot obstruct an embedding; this is the converse constraint that any host of a universal finitely presented group must itself have unsolvable word problem, which excludes host families
---

Let `U` be a finitely presented group containing every finitely presented
group, and let `H` be any group containing a copy of `U`. Then:

1. `H` has a finitely generated subgroup with unsolvable word problem. So if
   `H` is finitely generated, `H` has unsolvable word problem.
2. `H` contains `Z^k` for every `k`. So for every nonzero commutative ring `R`
   the cohomological dimension `cd_R(H)` is infinite. In particular `H` is not
   of type `FP` over any such `R`, and it does not have finite virtual
   cohomological dimension.
3. `H` contains every finite group, so it has finite subgroups of every order.

**Consequence: dead host families for `U`,** hence for
`every-finitely-presented-group-embeds-in-an-f-infinity-group` through a
single host of `U`. No finitely generated group with solvable word problem
can host `U`. That excludes:

- hyperbolic groups;
- groups acting properly and cocompactly on CAT(0) spaces;
- automatic groups;
- finitely generated linear groups;
- finitely presented residually finite groups, among them mapping class
  groups, `Aut(F_n)` and `Out(F_n)`;
- Thompson's groups `F`, `T`, `V` and the Brin--Thompson groups `nV`.

Item 2 alone excludes:

- every group of type `FP` over some nonzero ring `R`, since a finite-length
  projective resolution gives `cd_R < ∞`. Among them are the Bestvina--Brady
  groups `BB_L` and Leary's groups `G_L(S)` over `R`-acyclic flag complexes
  `L`, which are of type `FP` over `R` without being finitely presented;
- every group of finite virtual cohomological dimension, and every group
  acting properly on a finite-dimensional contractible complex.

Item 3 excludes groups with a bound on the orders of their finite subgroups.
So a recursively presented `FP_∞` host of `U`, as in
`universal-fp-group-embeds-in-rp-fp-infinity-group`, must be of type `FP_∞`
but not of type `FP` over any ring.

This does not rule out a host for an individual finitely presented group
`G`. It constrains a host that works for all of them at once, and a host of
`U` is exactly that.
