---
rg: 2
id: surjunctive-groups-are-quantitatively-surjunctive
kind: claim
title: Every surjunctive group has a uniform entropy-type deficit for injective maps into powers of proper subshifts
distinct_from:
  gottschalk-surjunctivity-conjecture: that concerns injective automata between equal full shifts; this asks, on a group already known to be surjunctive, for a deficit linear in the number of copies of a proper subshift, which the conjecture does not obviously give.
  injective-ca-images-have-full-single-site-entropy: that is a single-site entropy bound for images of the full shift over one alphabet; this compares injective maps into products of copies of a proper subshift with a free full-shift track.
artifacts:
  - research/artifacts/product-fibre-garden-of-eden-filter-2026-09-12.md
---

**OPEN.** Call `G` *quantitatively surjunctive* if the following holds for every finite alphabet `B`
and every proper subshift `Y` of `B^G`. There is `delta_Y > 0` such that for every finite alphabet `D`
and all `n >= 1`, `j, j' >= 0` with `(j' - j) log|D| < delta_Y n`, no injective cellular automaton maps
`(B^n x D^j)^G` into `Y^n x (D^(j'))^G`. The claim is that every surjunctive group has this property.

**What is known** (Section 3 of the artifact):
- a quantitatively surjunctive group is surjunctive (take `n = 1`, `j = j' = 0`);
- sofic groups are quantitatively surjunctive, with
  `delta_Y = -log(1 - |B|^(-|W|)) / (|W|^2 + 1)` for a pattern `r` on `W` missing from `Y`;
- if `G` is quantitatively surjunctive and `K` is sofic, then `G x K` is surjunctive.

## Attempts

- **Counting on sofic models (w4-free-pos-b).** It proves the sofic case.
  - **Lower bound.** Outputs determine inputs at good points.
  - **Upper bound.** Each track misses the pattern on a positive fraction of disjoint windows.
  - **Where it stops.** Both bounds need finite models of `G`.
- **Known surjunctive nonsofic groups.** They lie in the LEF permanence closure. Whether its operations
  preserve the property is not recorded. A proof along the finitary split-extension peeling would have
  to carry the deficit through each peeled stratum. That has not been attempted.
- **Restriction to invariant configurations (w5-quant-surj).** It settles every subshift missing a configuration
  invariant under a normal subgroup with sofic quotient (`quantitative-surjunctivity-constants-lift-from-quotients`).
  - **Constants.** Over every group, a subshift with `c_Y < |B|` constant configurations has constant `log(|B| / c_Y)`.
  - **Residually finite groups.** Periodic points give `-log(1 - |B|^(-|W|)) / |W|^2` with no sofic models.
  - **Where it stops.** The residue is the proper subshifts containing `Fix_N` for every normal `N` with sofic
    quotient. For groups with no nontrivial sofic quotient, finitely generated simple nonsofic groups included,
    that is every proper subshift containing all constant configurations. Restriction and fixed-point counts
    give nothing there.
  - **Theorem Q meets only the residue.** A Garden of Eden pattern whose subshift misses an `N`-invariant point is
    realized (`product-automata-images-contain-fibre-invariant-configurations`).
  - Artifact `research/artifacts/quantitative-surjunctivity-residue-2026-09-12.md`, Sections 1–2.
- **Zero margin and routes that die (w5-quant-surj).** Artifact Sections 3–4.
  - **Zero margin.** The case `j' <= j` is equivalent to surjunctivity. So surjunctivity already gives a margin
    of at least `log 2`, and the content of the claim is linear growth of the margin in `n`.
  - **Compactness.** A failure forces `n_i -> infinity`. A limit with infinitely many tracks is realized over
    every group by interleaving tracks, so no contradiction comes from the limit.
  - **Amplification.** Products keep the ratio, and composition adds margins.
  - **Recoding the output.** No injective automaton from a subshift containing the image into a smaller full
    shift exists over any group, since the image contains `|B|^n |D|^j` constant configurations.
  - **Clauses.** Surjunctivity forbids finite certificates of ratio `<= 0`. The claim forbids those below an
    unknown `delta`, and turning one kind into the other needs a recoding.
  - **Amenable Schreier graphs.** Følner counting on `H\G` gives constants when a positive density of vertices
    is `W`-injective for every `W`. By tensor-power amplification that makes `G` sofic, where the claim is known.
  - **Peeling.** In Theorem 0 of `research/artifacts/finitary-split-extension-surjunctivity-2026-09-11.md`, the
    transplants commute only with stabilizers `G_U`. The peeled stages compose with inverses of earlier stages,
    so none of them carries the subshift constraint. A constant would also have to grow with the block size
    `|Q_U|`, and the property gives no such bound.
- **Products with finite groups or `Z` (w5-quant-surj).** Artifact Section 5.
  - `G x F` for finite `F` and `G x Z` are surjunctive exactly when `G` is. So neither is equivalent to the
    claim unless the claim holds.
  - **The candidate equivalence.** "Quantitatively surjunctive iff `G x K` is surjunctive for every sofic `K`"
    holds forward by Theorem Q.
    - Its converse needs a construction from small-margin maps over `G` to strict automata over `G x K`, and
      none is known.
    - If the equivalence holds, this claim is equivalent to `products-with-a-sofic-factor-are-surjunctive`.
- **Rokhlin markers on subshift tracks (w7-quant-residue).** Artifact
  `research/artifacts/quantitative-surjunctivity-rokhlin-markers-2026-09-12.md`.
  - **Theorem.** An injection into `n` tracks missing patterns, plus a free track, lowers the Rokhlin entropy of the
    amplified Bernoulli shift by `sum_i eta_i / |W_i W_i^-1|`, at a marker cost of `log 3` per distinct window
    (`subshift-track-injections-lower-rokhlin-entropy`). The pushed-forward measure gives every invariant
    configuration measure zero, so the proof reaches the residue.
  - **Consequence.** Groups with maximal Bernoulli Rokhlin entropy are quantitatively surjunctive with
    `delta_Y = -log(1 - |B|^(-|W|)) / |W W^-1|`. A group that is not quantitatively surjunctive has finite Rokhlin
    supremum (`maximal-bernoulli-rokhlin-entropy-makes-groups-uqs`). Route
    `quantitative-surjunctivity-via-maximal-rokhlin-entropy`.
  - **Where it stops.** Every group known to have maximal Bernoulli Rokhlin entropy is sofic. So no new group becomes
    quantitatively surjunctive, and the residue stays open over every nonsofic group.
  - **Converse.** The candidate equivalence above is now the open claim
    `sofic-product-surjunctivity-forces-quantitative-deficits`. This claim holds iff that one and
    `products-with-a-sofic-factor-are-surjunctive` both hold (route
    `quantitative-surjunctivity-via-sofic-product-surjunctivity`). If that claim holds and this one fails, some sofic
    group lies outside the LEF permanence closure.
