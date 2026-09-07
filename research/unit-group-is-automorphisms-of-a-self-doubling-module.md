---
rg: 2
id: unit-group-is-automorphisms-of-a-self-doubling-module
kind: claim
title: The binary Leavitt unit group is the automorphism group of a module isomorphic to its own square
distinct_from:
  leavitt-gl-equals-el-and-perfect-unit-group: that identifies GL with EL and proves perfection by prefix codes; this is the module-theoretic description of the unit group itself and explains why matrix rank collapses, without comparing GL to EL.
  binary-leavitt-all-ranks-full-mf-radical: that is the analytic conclusion for the whole rank family; this is the structural reason the family is one group, with no approximation content.
  elementary-rank-descent-to-two: that descends higher ranks into rank two over any ring with a properly infinite unit, with no exhaustion; this needs the copies to exhaust the unit and gives an isomorphism rather than a normal-generation statement.
artifacts:
  - research/artifacts/rank-one-headline-review-2026-09-07.md
  - non_mf_groups_exist.tex
---

Let `R = L_(F_2)(1,2)` and let `M = R_R` be `R` as a right module over
itself.  Then

```text
End_R(M) = R,     M = M (+) M,     R^x = Aut_R(M),
```

the generators `s_1,s_2` and `t_1,t_2` being the insertion and extraction
maps of the decomposition.  Iterating, `M = M^(n)` for every `n >= 1`, so

```text
GL_n(R) = Aut_R(M^(n)) = Aut_R(M) = R^x.
```

A matrix is a description of an automorphism relative to a chosen
decomposition of `M`, and `M` already absorbs finite matrix coordinates.
That is why external matrix rank carries no information for this example.

The mechanism needs the two copies to exhaust `M`; a ring with a merely
properly infinite unit has two disjoint copies that need not exhaust it, and
there the corresponding statement is normal generation rather than
isomorphism.
