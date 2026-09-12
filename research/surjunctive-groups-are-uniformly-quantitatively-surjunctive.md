---
rg: 2
id: surjunctive-groups-are-uniformly-quantitatively-surjunctive
kind: claim
title: Every surjunctive group has a deficit for injective maps into products of proper subshifts, uniform over the missing patterns
distinct_from:
  surjunctive-groups-are-quantitatively-surjunctive: that allows the constant to depend on one fixed proper subshift repeated on every track; this lets different tracks miss different patterns, with a constant depending only on the alphabet and the window size, as twisted extensions require.
  gottschalk-surjunctivity-conjecture: that forbids injective non-surjective automata on one full shift; this forbids injections into many proper subshift tracks plus a slightly larger full track, which the conjecture does not obviously give.
artifacts:
  - research/artifacts/amenable-extension-surjunctivity-transfer-2026-09-12.md
---

**OPEN.** Every surjunctive group is uniformly quantitatively surjunctive, in the sense of
`amenable-extensions-of-uqs-groups-are-surjunctive`.

**Consequences.**
- **Amenable quotients.** Surjunctive-by-amenable groups are surjunctive (route
  `surjunctive-by-amenable-via-uniform-quantitative-deficit`).
- **Ascending HNN extensions** of surjunctive groups are surjunctive.
- **Relation to QS.** This implies `surjunctive-groups-are-quantitatively-surjunctive`.

## Attempts

- **Sofic groups.** The counting of `product-fibre-garden-of-eden-filter-2026-09-12.md`, Section 3, uses each track's
  missing pattern separately, and its constant depends only on `|B|` and `|W|`. So it gives the property for sofic
  groups. Recorded as a remark, not re-derived.
- **Heredity.** The property passes to subgroups and directed unions (artifact Proposition 3.1). So it is a local
  property. Proving it for every f.g. group in a class suffices for the class.
- **Where it dies: nonsofic surjunctive groups.** The Kun--Thom wreaths and doubles are surjunctive by marked-site
  peeling, which separates finite quotients stratum by stratum and carries no deficit. So neither this property nor
  its asymptotic version (enough for two-ended quotients) is known for any nonsofic group.
- **The zero-boundary case needs nothing.** When the decoder reads inside the kernel, plain surjunctivity suffices
  (`normal-surjunctive-decoder-memory-forces-surjectivity`). A counterexample to this claim must use decoders whose
  boundary cost is unbounded.
