---
rg: 2
id: q34-counterexample-necessary-conditions
kind: claim
title: A finitely presented simple group with no finitely presented simple MIF overgroup is infinite, not MIF, not highly transitive, has no type (A) action and infinitely many conjugacy classes, and has no lim-free hyperbolic action
distinct_from:
  fp-simple-groups-embed-in-fp-simple-mif-groups: that is BFFHZ Question 3.4 itself; this lists what a finitely presented simple counterexample to it must fail.
  bh-implies-pbh-iff-fp-simple-groups-satisfy-pbh: that shows a counterexample to Question 3.4 refutes permutational Boone--Higman; this constrains the shape of such a counterexample.
  pbh-passes-to-relative-free-group-automorphisms: that reformulates Question 3.4 for one group as membership of Aut_S(S * F_n) in the permutational class; this collects that reformulation together with the other known obstructions a counterexample must avoid.
artifacts:
  - research/artifacts/type-a-invariants-2026-09-13.md
---

**ESTABLISHED** through `q34-counterexample-necessary-conditions-proof`. Not
independently reviewed; no novelty claimed. It combines imported criteria with
two elementary claims landed alongside it.

## Statement

Let `S` be a nontrivial finitely presented simple group that embeds in no
finitely presented simple MIF group, i.e. a counterexample to BFFHZ Question 3.4
(`fp-simple-groups-embed-in-fp-simple-mif-groups`). Then:

1. `S` is infinite;
2. `S` is not MIF and not highly transitive;
3. `S` admits no action of type (A). Equivalently, every proper finitely generated
   subgroup `H` of `S` has infinitely many double cosets `H \ S / H`;
4. `S` has infinitely many conjugacy classes;
5. `S` has no isometric action of general type on a hyperbolic space whose induced
   action on the limit set is faithful and topologically free;
6. for every `n >= 2`, `Aut_S(S * F_n)` embeds in no group admitting an action of
   type (A).

## Where this leaves the search for a counterexample

- **Families cleared.** Every family recorded on main so far meets one of the
  mechanisms excluded above: Kac--Moody lattices through item 5, Leavitt unit
  groups through item 3 (census:
  `research/artifacts/q34-known-actors-coverage-2026-09-13.md`).
- **The ruled-out class.** For Cantor homeomorphism groups containing the
  commutator subgroup of `V_n`, BFFHZ Remark 3.5 calls them "obviously" highly
  transitive (text on MSI, l.550--566). The high-transitivity argument is not
  written out there and is not re-derived here, so it is not part of the statement.
- **Invariant census.** `research/artifacts/type-a-invariants-2026-09-13.md` records
  which properties of subgroups of type (A) actors were tested, and why none
  separates.
