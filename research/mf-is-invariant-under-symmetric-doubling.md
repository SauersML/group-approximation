---
rg: 2
id: mf-is-invariant-under-symmetric-doubling
kind: claim
title: Operator MF is invariant under symmetric amalgamated doubling
distinct_from:
  symmetric-double-weak-mf: that proves the positive direction for residually finite vertex groups by constructing a profinite regular completion; this is an if-and-only-if for every countable MF vertex group and uses Shulman's March 2026 group theorem directly.
  shulman-amalgam-mf-criterion: that is the compatible-corona criterion for a general C-star amalgam and warns that group MF need not make the full group C-star algebra MF; this is the special symmetric group theorem stated separately by Shulman, together with the elementary converse.
  mf-is-commensurability-invariant: that concerns finite-index inclusions; an amalgamated double usually contains either vertex group with infinite index and requires Shulman's symmetric-amalgam theorem for the forward implication.
artifacts:
  - research/artifacts/property-t-free-mf-envelope-calculus-2026-08-30.md
  - research/artifacts/shulman-2603-13564-verified.md
---

Let `G` be a countable group and `H <= G`.  For the symmetric double

```text
D = G *_H G,
```

one has the exact equivalence

```text
D is operator MF  <=>  G is operator MF.                (MSD1)
```

Thus symmetric amalgamated doubling cannot manufacture either side of the
MF/non-MF divide.  In particular it transports a non-MF seed upward, but it
cannot turn an MF seed into a non-MF group.

DERIVATION
mf-symmetric-double-invariance-proof
