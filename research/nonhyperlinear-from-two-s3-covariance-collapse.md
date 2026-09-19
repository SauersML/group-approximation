---
rg: 2
id: nonhyperlinear-from-two-s3-covariance-collapse
kind: route
title: Opposite fixed-S3 covariance bounds contradict hyperlinearity of the Leavitt unit group
target: non-hyperlinear-group
requires:
  - atlas-two-s3-covariance-collapse
  - leavitt-regular-atlas-separating-refinement
  - compiled-raw-source-word-nontrivial
  - raw-swap-forces-two-s3-covariance-energy
---

Assume the four prerequisites.  Let

```text
Q=L_(F_2)(1,2)^x.
```

Suppose for contradiction that `Q` is hyperlinear.  Apply
`leavitt-regular-atlas-separating-refinement` to the one-element set
containing the compiled raw source word.  Its nontriviality is
`compiled-raw-source-word-nontrivial`.  We obtain canonical regular-`A_8`
relative-unitary models `pi_n` such that

```text
max_(s in bar_S) ||pi_n(s)-1||_2 -> 0
```

and the raw source word stays at normalized-HS distance `sqrt(2)` from the
identity.

Let `a_n,b_n` be the two fixed `S_3` covariance defects.  The open collapse
claim gives

```text
a_n^2+b_n^2 -> 0.
```

But `raw-swap-forces-two-s3-covariance-energy`, applied to the same separating
models, gives

```text
a_n^2+b_n^2 >= 1/40-o(1).
```

Contradiction.  Therefore `Q` is not hyperlinear.  Since `Q` is an explicit
group, this establishes the program goal `non-hyperlinear-group`.
