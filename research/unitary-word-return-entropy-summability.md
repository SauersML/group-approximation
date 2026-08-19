---
rg: 2
id: unitary-word-return-entropy-summability
kind: claim
title: Random word return is summably dominated by representation-stratum entropy
artifacts:
  - research/artifacts/nonhyperlinear-random-presentation-and-matricial-separator-2026-08-18.md
  - research/artifacts/nonhyperlinear-finite-moment-sparsification-2026-08-18.md
  - experiments/random_word_return_strata.py
---

**SUPERSEDED AS A ROUTE TARGET.**  This claim is left open as a stronger
standalone analytic statement, but `finite-trace-profile-net-is-dimension-free`
shows that the random-relator proof never needs it when the relator menu and
short-word test are finite.

The old formulation asks for parameters for which dimension-by-dimension nets
`N_n` obey

```text
sum_n sum_(U in N_n) p_n(U)^m < Pr(SC).
```

That overcounts exactly the phenomenon the experiment exposed: normalized
trace/HS data are unchanged by repeated-block amplification, yet a separate
`U(n)^k` net counts every amplification again.  For a fixed finite word menu,
all relevant relator defects and short-word separations factor through a
single compact finite trace-profile cube.  `finite-moment-random-relator-sparsification`
uses one finite net of that cube and needs only a constant soundness fraction
for the relator menu.

## Historical attempts

- Avni--Glazer--Larsen dimension-uniform word-map small-ball estimates remain
  potentially useful for proving soundness of a proposed finite menu, but no
  longer have to pay for ambient `n^2` entropy.
- Noncommutative approximate-group inverse theory and quotient-moduli packing
  are likewise optional structure tools rather than prerequisites of the root
  route.
- `experiments/random_word_return_strata.py` remains useful as a falsification
  harness for proposed random-word soundness statements and records why raw
  dimension-only anti-concentration is false.

The live construction target replacing this node is
`robust-locally-satisfiable-relator-code`.
