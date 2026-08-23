---
rg: 2
id: actual-hard-prefix-s4-enumeration-proof
kind: route
title: Enumerate the actual Leavitt hard-prefix finite packets exactly
target: actual-hard-prefix-generates-s4-over-raw-s3
requires: []
artifacts:
  - experiments/atlas_actual_hard_prefix_finite_packet.py
---

Reconstruct the raw `K` generators and every hard prefix directly from the
stored chart words.  Evaluate them with exact binary Leavitt multiplication.
For a prefix word `g_1...g_r`, evaluate its group inverse from
`g_r^{-1}...g_1^{-1}`; use the Leavitt transpose only to construct the
separate word `q^star`.

Close the generated sets, comparing elements by common right refinement in
the Cuntz--Leavitt relation.  The replay finds four distinct prefix values,
the four order-24 histograms in `(AHP1)`, trivial `K`-core in every closure,
and the four order-168 histograms in `(AHP3)`.  Trivial core makes the
four-coset action faithful, identifying the order-24 closure with `S4`.

Replay with:

```text
python3 experiments/atlas_actual_hard_prefix_finite_packet.py
```
