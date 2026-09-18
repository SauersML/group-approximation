---
rg: 2
id: torsion-free-fp-groups-embed-in-fp2-conjugacy-finite-groups
kind: claim
title: "Every torsion-free group of type FP embeds in a torsion-free group of type FP_2 with finitely many conjugacy classes (an FP_2 form of Osin's theorem)"
distinct_from:
  osin-torsion-free-two-conjugacy-class-groups-exist: that imports finitely generated torsion-free groups with two conjugacy classes, with no finiteness beyond generation; this asks for FP_2 envelopes with finitely many classes, one for each torsion-free input of type FP.
  every-wp-group-embeds-in-fp-conjugacy-finite-group: that asked for finitely presented conjugacy-finite envelopes and is refuted by element orders; this restricts to torsion-free inputs, where element orders give no obstruction, and asks only for type FP_2, where recursive presentability is not forced.
  some-infinite-fp-torsion-free-group-has-finitely-many-classes: that asks for one infinite finitely presented torsion-free conjugacy-finite group; this asks for FP_2 ones, containing prescribed inputs.
---

**OPEN.** For every torsion-free group `H` of type FP there is a torsion-free group
`Γ ⊇ H` of type FP_2 with finitely many conjugacy classes.

Consumer: `uncountably-many-conjugacy-finite-fp2-groups-via-embedding`, and so,
through case (B) of `orbit-finite-fp2-affine-actors-are-faithful-ha2-actors`, the
first part of Problem 1.20.

**Screens.**

- *Element orders:* none; torsion-free groups have two orders.
- *Computability:* for Leary groups `G_L(S)` with `S` not recursively enumerable
  the input has unsolvable word problem, so the envelope `Γ` must not be
  recursively presented (`conjugacy-finite-recursive-presentation-solvable-wp`).
  This is allowed at type FP_2.
- *Residual properties:* an infinite conjugacy-finite group is not residually
  finite (a finite quotient has at most `k` classes, hence bounded order by
  Landau's theorem, so the finite residual has finite index), and every
  homomorphism from it to an abelian group has finite image. So `Γ` has finite
  abelianization.
- *Form:* by `fp2-iff-quotient-of-fp-group-by-perfect-normal-subgroup`, `Γ = P/N`
  with `P` finitely presented and `N` perfect. The task is to run an Osin-type
  conjugation of all elements into finitely many classes while each added family
  of relators generates a perfect normal subgroup.

**First falsifiable step.** Osin's groups arise as direct limits of relatively
hyperbolic groups, each step an HNN-type conjugation followed by small
cancellation quotients. Test whether the relators of one step can be chosen as
elements of a perfect subgroup, for example products of commutators of elements of
a fixed perfect finitely generated subgroup, as in Leary's use of perfect
`π_1(L)`. If the normal closure of each step's relators is perfect, the limit
group is `P/N` with `N` a union of perfect normal subgroups, hence perfect, and
the envelope is FP_2 once the first stage is finitely presented.

## Attempts

- 2026-09-18 (swarm-0917-w10-w10-z-last1, reframing): node created with the
  screens above; no construction attempted.
