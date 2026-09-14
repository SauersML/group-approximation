---
rg: 2
id: local-approximation-properties-are-decided-by-ec-groups
kind: claim
title: A local approximation property holds for all groups iff it holds for one existentially closed group, iff it holds for every existentially closed group
distinct_from:
  local-approximation-properties-are-marked-closed: that shows failures of a local approximation property are open and have finitely presented witnesses; this shows a single fixed model-theoretic object, any existentially closed group, fails the property as soon as any group does.
  surjunctivity-is-axiomatized-by-rectangle-clauses: that shows existentially closed groups decide Gottschalk's conjecture, because a surjunctivity failure is an existential sentence; this runs the same transfer for every table-defined approximation property, where a failure is a finite table with no model.
  non-hyperlinear-group: that is the existence question; this reduces it to hyperlinearity of any one existentially closed group, without deciding it.
---

**ESTABLISHED** through `ec-groups-decide-local-approximation-properties-proof`.
Elementary; no novelty is claimed.  The transfer is the one used for
surjunctivity in `surjunctivity-is-axiomatized-by-rectangle-clauses`.

**Statement.**  Let `M` be any model predicate, and `P_M` the associated local
approximation property of `local-approximation-properties-are-marked-closed`.
Examples are sofic, hyperlinear, operator-MF, LEF, weakly sofic and linear
sofic.  The following are equivalent:
- (a) every group has `P_M`;
- (b) some existentially closed group has `P_M`;
- (c) every existentially closed group has `P_M`.

The same equivalence holds among torsion-free groups, with (b) and (c) about
groups existentially closed in the class of torsion-free groups.

**Consequences.**
- A non-hyperlinear group exists iff every existentially closed group is
  non-hyperlinear, iff some countable existentially closed group is.  So any
  one countable existentially closed group is a universal test object for
  `non-hyperlinear-group`, and likewise for every other table-defined
  approximation property.
- No existentially closed group is computable, so these test objects pass the
  filter of `computable-groups-have-no-locally-universal-group-factor`
  unconditionally.  The proof is on the route.
- Nonsofic groups exist, so every existentially closed group is nonsofic
  (`existentially-closed-groups-are-nonsofic`).
