---
rg: 2
id: kun-thom-full-group-balls-embed-in-permanence-closure
kind: claim
title: Every finite subset of the Kun--Thom product-action alternating full group embeds as a partial table into the permanence closure
distinct_from:
  permanence-closure-contains-fg-simple-nonsofic-group: that asks for some finitely generated simple nonsofic group in the permanence closure; this is the local-embedding step for one candidate, which is the only way such a group can enter.
  strict-pairs-transfer-to-table-realizations: that proves local embeddability into surjunctive groups preserves surjunctivity; this asks whether one specific group is locally embeddable into the permanence closure.
artifacts:
  - research/artifacts/kun-thom-alternating-full-group-2026-09-12.md
---

**OPEN.** Let `A(Y)` be as in `kun-thom-product-action-alternating-full-group-is-nonsofic`. Then every finite subset
of `A(Y)` embeds as a partial multiplication table into a group of the closure `S*` of
`gottschalk-counterexamples-lie-outside-the-permanence-closure`.

Then `A(Y)` lies in `S*` by (O3) and is surjunctive.

## Attempts

A ball must carry three things (artifact Section 4):
- noncommuting cylinder permutations at overlapping windows;
- base parts that vary from piece to piece;
- a nonsofic witness ball of the wreath.

- **Permutational wreaths with finite lamps (O4), marked-site assignment.** It dies at overlapping windows: lamps at
  distinct sites commute, while both orders of a noncommuting product lie in any ball of radius 4. Partial tables may
  assign differently, so this is not an obstruction.
- **Cylinder-permutation extension `H_fin semidirect G`.** It misses the varying base parts, and no operation of `S*`
  reaches it:
  - `H_fin` is simple and locally finite, so detection (A1) fails for O4;
  - transplant coset spaces have unbounded marks, so peeling has nothing finite to work with.
- **Layered wreaths over `K wr Sym(G/K)`.** They are in `S*`, but vary base parts only along layers, not along
  configuration cylinders.
- **Where it stops.** A permanence theorem for topological full groups of lamp actions is needed. Even the
  constant-base-part group `H_fin semidirect G` is not covered.
- **Negative route.** A finitely presented infinite simple nonsofic subgroup of `A(Y)` would refute this node through
  the evasion theorem. None is known.
