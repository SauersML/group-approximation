---
rg: 2
id: deligne-sep7-triple-radical-via-all-cover-formula
kind: route
title: Specialize the simultaneous annihilator formula at covering degree three
target: deligne-triple-cover-exact-mf-radical
requires:
  - deligne-sep7-all-cover-mf-radical-classification
  - deligne-nontrivial-maslov-opnorm-sectors-are-empty
artifacts:
  - research/artifacts/deligne-sep7-all-cover-mf-classification.md
---

The second prerequisite says that neither `1/3` nor `2/3` belongs to the
norm-parameter subgroup. Its intersection with `(1/3)Z/Z` is therefore
`{0}`. The annihilator formula in the first prerequisite makes the radical
of `E_3` the entire order-three covering kernel, as required.

More generally the same input forces the finite subgroup order `m` to be
coprime to three. The formula then also computes, for every `a>=1`,

```text
Rad_MF(E_(3^a))=<z_(3^a)>,
Rad_MF(E_(2*3^a))=<z_(2*3^a)^2>.
```

The new unconditional classification is a reusable input, while the
sector-emptiness prerequisite remains open.
