---
rg: 2
id: compiled-raw-source-word-nontrivial
kind: claim
title: The compiled two-chart raw source word is nontrivial in the Leavitt unit group
distinct_from:
  raw-swap-forces-two-s3-covariance-energy: That is a quantitative normalized-HS lower bound in regular atlas models; this is the exact algebraic fact that the fixed 25-syllable source word maps to a nonidentity element of Q.
artifacts:
  - experiments/atlas-raw-compressor-source-words.json
  - notes/TRUE_RAW_SWAP_FULL_BRANCH_ROUTING.md
  - GroupApproximation/Leavitt/RawSwapCompressors.lean
---

Let `r_raw in K_1*K_2 ~= A_8*A_8` be the fixed 25-syllable word recorded as
`raw_source_word` in `experiments/atlas-raw-compressor-source-words.json`.
Under the atlas map to

```text
Q=L_(F_2)(1,2)^x
```

it evaluates to the scalarized raw swap

```text
w = x_14(s_1) x_41(-t_1) x_14(s_1).
```

This element is nonidentity in `Q`.
