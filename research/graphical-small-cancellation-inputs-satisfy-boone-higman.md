---
rg: 2
id: graphical-small-cancellation-inputs-satisfy-boone-higman
kind: claim
title: Every finitely generated graphical small cancellation group with finite components and solvable word problem embeds in a finitely presented simple group
distinct_from:
  boone-higman-conjecture: that is all decidable inputs; this is one geometric family, chosen because it is far from linear and from hyperbolic and it contains the known non-exact decidable groups.
  fp-simple-nonexact-group: that asks for one non-exact finitely presented simple group; this claim implies it (route fp-simple-nonexact-group-via-graphical-small-cancellation-bh), but not conversely.
  fp-simple-groups-with-arbitrarily-complex-word-problem: that asks for finitely presented simple groups of unbounded word-problem complexity; this claim implies it (route complex-fp-simple-groups-via-small-cancellation-bh), but not conversely.
artifacts:
  - research/artifacts/gq-bh-bh-graphical-sc-hard-test-case.md
---

**OPEN.** Let `Γ` be a graph with finite connected components, possibly infinitely many,
labelled over a finite alphabet `S` so that the labelling satisfies the graphical
`Gr'(1/6)` condition. Let `G(Γ) = <S | labels of closed paths of Γ>`. If `G(Γ)` has
solvable word problem, then `G(Γ)` embeds in a finitely presented simple group.

This contains every classical `C'(1/6)` group with solvable word problem, since those are
the case where each component is a cycle.

## Why it is a hard test case, and not just a special case

**It implies two open existence statements about finitely presented simple groups.**
1. The family contains a residually finite, non-exact group with solvable word problem:
   Osajda's graphical small cancellation group from a recursive input
   (`decidable-residually-finite-non-exact-group-exists`). Exactness passes to subgroups.
   So this claim implies `fp-simple-nonexact-group`. The route is
   `fp-simple-nonexact-group-via-graphical-small-cancellation-bh`.
2. The subfamily of two-generator classical `C'(1/6)` groups realizes every recursive
   word-problem complexity (`small-cancellation-groups-realize-every-wp-complexity`).
   So this claim implies `fp-simple-groups-with-arbitrarily-complex-word-problem`.
   The route is `complex-fp-simple-groups-via-small-cancellation-bh`.

**The known hosts fail on it.** The details are in the artifact.
- **Linear hosts.** Linear groups over commutative rings are exact
  (`commutative-ring-linear-groups-have-property-a`), so they miss Osajda's group.
  Linear groups over fields also have uniformly bounded word problem, so they miss the
  hard `G_A`.
- **Hyperbolic, rational-homeomorphism and contracting-RSG hosts.** Each has one recursive
  word-problem bound (`complexity-bounded-host-classes-are-not-universal`,
  `rational-homeomorphism-subgroups-have-exponential-wp`), so each misses some
  classical `C'(1/6)` input. Hyperbolic groups are also exact, so they miss Osajda's
  group.
- **Haagerup hosts.** The Thompson groups `F ≤ T ≤ V`, the Higman--Thompson groups and
  all SFT topological full groups carry no weakly embedded expander
  (`haagerup-hosts-carry-no-weak-expander`). So they miss every expander-type monster in
  the family.
- **Any single host.** No single finitely generated group with solvable word problem
  contains every member of the family (item 5 of the complexity node).

## What is known

- **Finitely many components.** Then `G(Γ)` is finitely presented and hyperbolic.
  This is classical graphical small cancellation theory (Ollivier; Gruber), cited and
  not re-read at source. So `G(Γ)` satisfies Boone--Higman by Belk--Bleak--Matucci--Zaremsky,
  arXiv:2309.06224, whose intermediate host is on main as
  `hyperbolic-groups-embed-in-contracting-rsgs`.
- **Infinitely many components.** Nothing is known, for any member that is not already a
  subgroup of a hyperbolic group, a linear group, or another known host. That covers
  the non-exact members and the classical members of high word-problem complexity.

## Attempts

1. **bh-graphical-sc, 09-18.**
   - *The outcome.* No embedding was found, so the claim stays OPEN. The two implications
     above and the complexity-realization node were established.
   - *What any proof must supply.* A host family of unbounded word-problem complexity.
     For the non-exact members it must also be non-exact and non-Haagerup.
   - *Why the lead candidates don't finish it.*
     - Twisted Brin--Thompson groups with hard type (A) actors are the only candidate
       family in the graph for unbounded complexity (`arbitrarily-complex-fp-simple-via-hard-type-a-actors`),
       and their actor node is itself OPEN.
     - `L^x = L_(F_2)(1,2)^x` is the only finitely presented simple group known here not
       to be Haagerup.
     - Neither is known to contain any member with infinitely many components.
