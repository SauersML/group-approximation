---
rg: 2
id: sofic-product-surjunctivity-forces-quantitative-deficits
kind: claim
title: A group whose products with all sofic groups are surjunctive is quantitatively surjunctive
distinct_from:
  surjunctive-groups-are-quantitatively-surjunctive: that assumes only surjunctivity; this assumes surjunctivity of every product with a sofic group, which that claim implies through Theorem Q, and asks for the converse implication.
  products-with-a-sofic-factor-are-surjunctive: that asks whether a surjunctive group times a sofic group is surjunctive; this asks whether that property of one group already forces its quantitative deficit.
artifacts:
  - research/artifacts/quantitative-surjunctivity-rokhlin-markers-2026-09-12.md
---

**OPEN.** Let `G` be a group such that `G x K` is surjunctive for every sofic group `K`. Then `G` is quantitatively
surjunctive in the sense of `surjunctive-groups-are-quantitatively-surjunctive`.

**Place in the graph** (Section 4 of the artifact).
- **Per group.** The converse implication is Theorem Q, Section 3 of
  `research/artifacts/product-fibre-garden-of-eden-filter-2026-09-12.md`. So this claim says that the two properties
  coincide on every group.
- **Equivalence.** `surjunctive-groups-are-quantitatively-surjunctive` holds iff this claim and
  `products-with-a-sofic-factor-are-surjunctive` both hold (route
  `quantitative-surjunctivity-via-sofic-product-surjunctivity`).
- **LEF permanence closure.** For surjunctive `G`, `products-with-lef-permanence-closure-factors-are-surjunctive`
  makes `G x K` surjunctive for every `K` in `Cl(LEF)`.
  - If every sofic group lies in `Cl(LEF)`, the hypothesis is plain surjunctivity, and this claim is the quantitative
    claim itself.
  - If this claim holds and the quantitative claim fails, some sofic group lies outside `Cl(LEF)`. No such group is
    known.

## Attempts

- **Form of a counterexample (w7-quant-residue).** A counterexample is countably infinite, since finite groups meet the
  bound by counting. It is surjunctive (take `K = 1`) and not quantitatively surjunctive.
  - By part 3 of `maximal-bernoulli-rokhlin-entropy-makes-groups-uqs` its Rokhlin supremum is finite.
  - By item 3 of `seward-per-group-rokhlin-entropy-of-bernoulli-shifts`, `P x G` has Rokhlin supremum `0` for every
    countable `P` with arbitrarily large finite subgroups.
- **Inverting the transplant (w7-quant-residue).** Theorem Q transplants an automaton over `G x K` onto `G` along a
  sofic model of `K`, and the free track pays for the model's defects.
  - **Inversion.** Running it backwards builds a strict automaton over some `G x K` from small-margin maps over `G`,
    by laying the tracks along vertices of finite models of `K` and correcting the defects.
  - **Where it dies.** Models realizing the multiplication of `K` exactly on growing balls make `K` LEF, and then
    `G x K` is already surjunctive. So the defects must be hidden inside the margin, and no mechanism for that is known.
- **What a refutation needs.** A surjunctive group that is not quantitatively surjunctive and whose products with all
  sofic groups are surjunctive. Products with `Cl(LEF)` are automatic, so the refutation must also handle every sofic
  group outside `Cl(LEF)`, where no example is known.
