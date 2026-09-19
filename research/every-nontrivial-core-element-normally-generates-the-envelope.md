---
rg: 2
id: every-nontrivial-core-element-normally-generates-the-envelope
kind: claim
title: One normal generator inside a simple core upgrades to all of them, and forces the envelope to be perfect
distinct_from:
  proper-normal-subgroups-miss-the-normally-generating-core: that is the lattice statement -- proper normal subgroups avoid the core; this is the upgrade of the hypothesis itself, that the single prescribed normal generator can be replaced by ANY nontrivial core element, plus the perfectness and infinite-quotient consequences. Neither is used to prove the other.
  simple-lamp-radical-one-relation: that says one lamp element normally generates a radical inside a specific wreath group and measures a presentation-theoretic distance; this says every nontrivial element of an abstract simple core normally generates the whole ambient group.
  defect-normally-generates-torsion-free-quotient: that identifies one element as a normal generator of one constructed subgroup; this quantifies over all nontrivial elements of the core and concludes perfectness of the ambient group.
artifacts:
  - research/artifacts/boone-higman-audit-2026-08-17.md
---

Keep the hypotheses of
`proper-normal-subgroups-miss-the-normally-generating-core`: `S` nontrivial
simple, `S <= Gamma`, and `Gamma = <<s>>_Gamma` for some `1 != s in S`.
Then:

1. **every** `1 != t in S` satisfies `Gamma = <<t>>_Gamma`;
2. if `S` is infinite, `Gamma` is perfect, `[Gamma, Gamma] = Gamma`;
3. if `S` is infinite, every proper quotient of `Gamma` is infinite.

Clause 2's hypothesis is free: by
`boone-higman-thompson-simple-envelope` the simple core may be taken infinite
at no cost, by feeding `G × Z` to the envelope theorem instead of `G`.

## What this rules out and what it does not

Together with `proper-normal-subgroups-miss-the-normally-generating-core`
this says the envelope can be arranged finitely presented, property (T),
perfect, with no nontrivial finite quotient, with every proper quotient
infinite, and with every nontrivial element of a distinguished simple
subgroup a normal generator of the whole group.  That is a great deal of
rigidity, and it is worth being explicit that **none of it bears on the
open question**.

The obstruction in `ck-envelope-has-a-finitely-normally-generated-maximal-kernel`
is a *compactness* property of the normal lattice — does some maximal element
admit a finite normal generating set — and every clause above is a
*non-existence* statement about small quotients.  A group can have no small
quotients at all and still have every maximal normal subgroup infinitely
normally generated; nothing here excludes that, and this audit found no
argument connecting the two.  The clauses are recorded because they are
true, cheap, and worth not rediscovering, not because they are progress.
