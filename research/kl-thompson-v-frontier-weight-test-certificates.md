---
rg: 2
id: kl-thompson-v-frontier-weight-test-certificates
kind: claim
title: Exact positive weight-test certificates settle NCERT frontier classes of the length-six and length-seven census over V
distinct_from:
  kl-thompson-v-short-generator-words-certified-injective: that certifies 85432 census classes by finite coefficients, the four-light-corner and three-light-corner weights, powers and retractions onto V; this certifies further classes, all from its 95770-class frontier, each by its own explicit rational weight passing the general weight test.
  kl-relative-weight-test-gives-injectivity: that is the general implication from a passing weight to injectivity over any group; this is its exact application, word by word, to listed census words over V.
  kl-holds-over-thompson-v: that is injectivity for every nonsingular word over V; this is a finite list of words.
artifacts:
  - research/artifacts/kl-thompson-v-census-weight-test-2026-09-16.md
  - experiments/kl-violating-equation-over-thompson-v-2026-09-16/weight_certificates.txt
  - experiments/kl-violating-equation-over-thompson-v-2026-09-16/verify_weight.py
---

Let `V` be Thompson's group with the Bleak--Quick generators `a = (00 01)`,
`b = (01 10 11)`, `c = (1 00)`, `B = b^(-1)`, acting on `{0,1}^N` by prefix
replacement. Let `W` be the census of
`kl-thompson-v-short-generator-words-certified-injective`: cyclically reduced words

```text
w = g_0 t^(e_0) g_1 t^(e_1) ... g_(n-1) t^(e_(n-1)),
```

with `e_i = +-1`, `n in {6, 7}`, `0 < sum e_i < n`, `g_i in {a, b, B, c}` at
sign changes and `g_i in {1, a, b, B, c}` otherwise, up to rotation and
`w -> sigma(w^(-1))`.

**The claim.** Each of the `NCERT` classes listed in
`experiments/kl-violating-equation-over-thompson-v-2026-09-16/weight_certificates.txt`
is a frontier class of that census (not among its 85432 certified classes).
For each of them `V -> (V * <t>)/<<w>>` is injective.

Each line `<id> <word> WEIGHT theta=q_0,...,q_(n-1)` gives rational weights on
the corners, where corner `i` sits between `t^(e_(i-1))` and `t^(e_i)` and
carries `g_i`. The weights satisfy:
- `q_i >= 1/4` for every `i`;
- (WT1) `sum_i (1 - q_i) >= 2`;
- (WT2) every cyclically reduced closed path in the star graph of `w` whose
  label is trivial in `V` has weight at least `2`.

By class:

TABLE-PLACEHOLDER

So the census now certifies `85432 + NCERT = NTOTAL` of its `181202` classes
and leaves `NREMAIN` open.
