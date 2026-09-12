---
rg: 2
id: compiled-raw-source-word-nontrivial-proof
kind: route
title: Compile the source word and use exact branch routing
target: compiled-raw-source-word-nontrivial
requires: []
artifacts:
  - experiments/atlas-raw-compressor-source-words.json
  - notes/TRUE_RAW_SWAP_FULL_BRANCH_ROUTING.md
  - GroupApproximation/Leavitt/RawSwapCompressors.lean
---

The committed compiler certificate
`experiments/atlas-raw-compressor-source-words.json` verifies that the fixed
25-syllable free-product word evaluates under the two atlas charts to

```text
w=x_14(s_1)x_41(-t_1)x_14(s_1).
```

The exact routing identities in `TRUE_RAW_SWAP_FULL_BRANCH_ROUTING` give, for
an allowed auxiliary index `j` and coefficient `a=1`,

```text
w x_0j(s_1) w^(-1) = x_4j(-1).
```

The two displayed root elements lie in different Steinberg root subgroups and
are distinct (their standard elementary-matrix images have their unique
off-diagonal entries in different positions).  If `w=1`, conjugation by `w`
would fix `x_0j(s_1)` and force those two distinct root elements to be equal.
Therefore `w!=1`, and hence the compiled source word is nontrivial in `Q`.
