---
rg: 2
id: atlas-seven-word-a9-a10-exclusion
kind: claim
title: Six boundary words plus collision 19243 exclude every natural A9 and A10 regular-margin two-chart model
distinct_from:
  atlas-word-19243-is-kernel-relation: that proves one interior word is genuine; this combines it with the exact first-failure structure of the finite overgroup scans.
  atlas-two-s3-covariance-collapse: that asks for a dimension-free matricial theorem; this is a finite exact exclusion in the two smallest natural alternating overgroups.
artifacts:
  - experiments/atlas-a9-two-chart-scan-v2.json
  - experiments/atlas-a10-two-chart-scan.json
---

**ESTABLISHED, exact finite scan.**  Let the six boundary indices be

```text
B_6={0,2,11,30,44,55}
```

in the canonical ordering of the `234` radius-five boundary words, and add
the interior collision word `q_19243`.

For each `n in {9,10}`, embed the first labeled `A_8` as the alternating group
on the first eight points of `A_n` and let the second labeled chart range over
all `S_n`-conjugates, modulo the pointwise chart centralizer.  This includes
both inner and outer labelings of the second `A_8`.

Then **no** relative chart position satisfies all seven words.

The archived exhaustive scans tested

```text
n=9:   362880 chart positions,
n=10: 1814400 chart positions.
```

Their first-boundary-failure histograms have support exactly

```text
0,2,11,30,44,55.
```

Hence every chart position that fails the full `234`-word boundary packet
already fails one of the six words in `B_6`.  In each degree exactly one chart
position survives all `234` boundary words, and the archived combined scan
shows that collision `19243` is nontrivial at that survivor.  Therefore the
seven-word packet has zero survivors.

Because the generated finite groups are centerless in these geometries,
checking `q_19243=1` is exactly the same as checking its canonical centrality
condition.  Passing to the left regular representation of a survivor would
have given a genuine finite-dimensional regular-`A_8`-margin model, so the
absence of survivors is an exact representation-theoretic exclusion rather
than a numerical screen.

## Research consequence

The all-irrep tangent certificate used the nearby five-word set
`{0,11,30,44,55}`.  Adding only boundary word `2` and the single interior word
`19243` already kills every natural degree-nine and degree-ten far branch.
This seven-word packet is therefore the first concrete candidate that should
be fed to `atlas-spectral-range-hall-certificate` or another global
matricial-coercivity search: it simultaneously carries the local tangent gap
and exact finite-overgroup branch exclusion.
