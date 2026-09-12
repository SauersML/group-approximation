---
rg: 2
id: gottschalk-counterexamples-lie-outside-the-permanence-closure
kind: claim
title: No finitely presented infinite simple nonsofic group embeds in the permanence closure of the sofic groups
distinct_from:
  surjunctive-nonsofic-group-exists: that exhibits surjunctive nonsofic groups, all inside the permanence closure; this names the closure and shows the binary Leavitt unit group and every group containing it lie outside, so no permanence theorem decides them.
  strict-pairs-transfer-to-table-realizations: that moves one strict certificate along realizations of its tables; this determines which groups the available surjunctivity theorems reach and proves that a finitely presented simple nonsofic group escapes all of them.
artifacts:
  - research/artifacts/gottschalk-table-realization-and-evasion-2026-09-12.md
---

**ESTABLISHED** by `permanence-closure-evasion-proof`.

**The closure.** `S*` is the smallest class of groups that contains every sofic
group and is closed under:

- (O1) subgroups;
- (O2) groups whose finitely generated subgroups all lie in `S*`;
- (O3) groups locally embeddable into `S*` (`strict-pairs-transfer-to-table-realizations`);
- (O4) split extensions with a finitary site structure over a group of `S*`
  (`finitary-split-extension-surjunctivity-permanence`). These include permutational
  wreaths with residually finite lamps, and group doubles;
- (O5) graphs of groups admitting a homomorphism into a group of `S*` that is
  injective on vertex groups (`graph-folds-over-surjunctive-groups-are-surjunctive`);
- (O6) graph wreath products with LEF lamps over a group of `S*`
  (`lef-lamp-graph-wreaths-are-surjunctive`);
- (O7) split extensions with finitely generated residually finite kernel over a
  group of `S*` (Arzhantseva--Gal 2020, Theorem 1).

Every group in `S*` is surjunctive.

**Theorem.** Let `Q` be an infinite, finitely presented, simple, nonsofic group.
Then no group in `S*` contains a copy of `Q`.

**Consequences.**
- `L_(F_2)(1,2)^x` is infinite, finitely presented, simple and nonsofic
  (`fp-simple-nonsofic-group`). So no group containing it lies in `S*`, and no
  combination of the surjunctivity permanence results now available decides such
  a group.
- The surjunctive nonsofic groups found so far lie inside `S*`:
  - the Kun--Thom wreaths and doubles;
  - the LEF graph wreaths;
  - the free-lamp amalgams `G *_Gamma (Gamma × K)` with `K` LEF, which are graph
    wreaths with empty graph.
- A Gottschalk counterexample needs a memory group, and a table group, outside
  `S*`.

**Scope.** This does not claim that `S*` contains every surjunctive group. Nor does
it claim that the Leavitt unit group is not surjunctive. It only records that every
existing positive method stops short of that group. Proof: Section 3 of the linked
artifact.
