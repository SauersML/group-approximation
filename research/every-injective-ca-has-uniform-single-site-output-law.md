---
rg: 2
id: every-injective-ca-has-uniform-single-site-output-law
kind: claim
title: Every injective cellular automaton sends uniform Bernoulli input to a uniform single-site output law
distinct_from:
  every-injective-ca-preserves-uniform-bernoulli-measure: that asks the whole image measure to be the uniform product measure; this asks only that the one-site marginal be uniform, which looks much weaker and is equivalent to the goal by the anchor construction.
  gottschalk-surjunctivity-conjecture: that is surjunctivity on full shifts; this is one site statistic, equivalent to it through two routes that form an intended cycle.
artifacts:
  - research/artifacts/finitary-generation-single-site-criterion-2026-09-12.md
---

**OPEN.** For every group `G`, every finite alphabet `A`, and every injective automaton `kappa` on `A^G`,
the law of `kappa(x)(e)` under the uniform product measure is uniform on `A`.

Group by group, and over all alphabets, this is equivalent to surjunctivity:
- `uniform-single-site-output-law-from-gottschalk`: injective automata are bijective, and bijective
  automata preserve the uniform product measure;
- `gottschalk-via-uniform-single-site-output-law`: by
  `strict-automata-give-injective-ca-with-skewed-site-marginals`, a strict automaton gives an injective
  automaton on `A^(k+1)` with non-uniform site law.

The two routes form an intended cycle through the goal, so neither establishes anything.

## Attempts

- **Known cases.** It holds for sofic groups, through `sofic-groups-are-surjunctive` and the first route.
  So it holds for amenable groups too.
- **Counting stops.** Let `E` be the memory of a left inverse. Then `|F| log |A| <= |F E| H`. Counting
  therefore certifies only `H >= log |A| sup_F |F|/|F E|`, which is below `log |A|` on nonamenable groups.
- **What the criterion adds.** On a simple Kazhdan host a proof must control one marginal of one image
  process, not the whole image measure. No mechanism for that is known on nonsofic hosts.
- **Small memory (w4-bal-census, artifact `small-memory-balance-census-2026-09-12.md`).**
  - **Settled.** Two memory elements over every alphabet, because the memory group is cyclic. Two
    symbols with at most three memory elements, over every group
    (`binary-three-address-injective-automata-have-balanced-rules`). The proof uses constant tests,
    prescribed flips and a double flip, and no finite models.
  - **Sidon memory.** On two symbols, if the quotients `m^-1 m'` are distinct, an unbalanced rule
    has an invisible single flip (`binary-unbalanced-rules-on-sidon-memory-are-not-pre-injective`).
    So a counterexample needs a relation `m^-1 m' = n^-1 n'`.
  - **Stops at rigid three-symbol rules**, where no pair is blind in every coordinate
    (`ternary-three-address-injective-automata-have-balanced-rules`).
    - Smallest instance: `x - y + z` patched at `(0,2,2)`.
    - By `avoidable-patches-of-affine-rules-inherit-linear-injectivity`, it needs `1 - a + b` to be a
      unit of `F_3[G]`.
  - **Stops at two symbols with placements that are Sidon in no group**
    (`binary-four-address-injective-automata-have-balanced-rules`).
