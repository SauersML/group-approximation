# Invariants of subgroups of type (A) actors: search for a separating property (lane type-a-invariants, 2026-09-13)

**Goal.** Refute permutational Boone--Higman (PBH) through BFFHZ Question 3.4. That
needs a property `P` held by every subgroup of every group with an action of type
(A), the class `B_A`, and some finitely presented simple group without `P`.

**Result.** No separating property was found. What landed shrinks the frontier:

- `fp-simple-type-a-actions-iff-finite-bi-index-subgroups`;
- `centerless-fp-finitely-many-conjugacy-classes-gives-pbh`;
- `q34-counterexample-necessary-conditions`.

## Candidate properties tested

Each candidate is listed with the reason it does not separate.

1. **Solvable word problem.** It holds for every subgroup of a type (A) actor
   (Zaremsky Corollary B, `type-a-action-gives-boone-higman-for-subgroups`). It
   also holds for every finitely presented simple group, by
   `simple-envelope-forces-solvable-word-problem`. No separation.
2. **Decidable point-stabilizer membership.** Point stabilizers of a type (A)
   action have decidable membership (`finite-bi-index-subgroups-have-decidable-membership`,
   consequence 1).
   - A subgroup `K` of an actor inherits only a faithful computable action whose
     stabilizers `K ∩ Stab_G(x)` are decidable in `K`.
   - Every finitely generated group with solvable word problem already has one: its
     regular action, with trivial stabilizers.
   - No separation.
3. **Decidable membership for all finitely generated subgroups.** Not a property
   of `B_A`.
   - Thompson's `V` lies in `B_A` (BFFHZ Remark 3.5, highly transitive).
   - It contains `F_2 x F_2`: standard, e.g. `V x V <= V` and `F_2 <= V`, not
     re-read here.
   - Mihailova subgroups of `F_2 x F_2` have undecidable membership (standard;
     Attempt 4 of `type-a-actors-with-arbitrarily-hard-word-problem` records the
     same example inside `2V`).
   - Since `B_A` is closed under subgroups, any separating property must hold for
     all subgroups of `V`.
4. **A uniform recursive word-problem bound.** This separates PBH exactly when type
   (A) actors share one recursive bound.
   - If they did, `complexity-bounded-host-classes-are-not-universal` gives a
     two-generated decidable group outside `B_A`, so PBH fails.
   - That is the OPEN `type-a-actors-with-arbitrarily-hard-word-problem`, whose
     route `hard-type-a-actors-from-permutational-boone-higman` already records
     the PBH direction.
   - For Question 3.4 in particular, it would also need a finitely presented simple
     group beyond the bound: OPEN `fp-simple-groups-with-arbitrarily-complex-word-problem`.
   - No new separation.
5. **Finitely many orbits of pairs in the group's own actions.** Constraints such as
   `closed-mcg-pair-orbit-finite-actions-have-large-stabilizers` restrict the actor
   itself. They do not restrict groups that merely embed in an actor. For simple
   groups, the landed equivalence reduces "S is its own actor" to a finite
   bi-index subgroup. No obstruction transfers to overgroups.
6. **Mixed identities and high transitivity.** Every finitely presented simple MIF
   or highly transitive group is in `B_A` (Theorem C). A counterexample has neither
   (item 2 of `q34-counterexample-necessary-conditions`). But non-MIF finitely
   presented simple groups such as `T` are in `B_A` through `V`, so "has a mixed
   identity" does not separate.
7. **Conjugacy classes.** Finitely many classes plus trivial center gives a type (A)
   action of `G x G` (landed). No finitely presented infinite group with finitely
   many classes is known (BFFHZ l.380--381), so this condition clears no new
   finitely presented simple group. It only adds item 4 of the necessary
   conditions.

## The frontier after this lane

A finitely presented simple counterexample to Question 3.4 must satisfy all of
the following:

- infinite;
- not MIF, not highly transitive;
- every proper finitely generated subgroup of infinite bi-index;
- infinitely many conjugacy classes;
- no lim-free general type hyperbolic action;
- `Aut_S(S * F_n)` outside `B_A` for all `n >= 2`.

No finitely presented simple group is known to satisfy them all. The first
condition to test on a candidate is item 3: exhibit a finitely generated subgroup
with finitely many double cosets, or prove none exists.

## Sources pinned

- BFFHZ, arXiv:2503.21882v2, text on MSI
  `/scratch.global/sauer354/bh-outfn-mcg/2503.21882v2.txt`:
  - l.354--381: Observation 2.4 and the conjugacy-class remark;
  - l.545--566: Question 3.4 and Remark 3.5.
- Zaremsky, arXiv:2405.18354: the type (A) definition and Corollary B, as quoted on
  `type-a-action-gives-boone-higman-for-subgroups`.
