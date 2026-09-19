---
rg: 2
id: nonhyperlinear-from-one-cut-atlas-extraction
kind: route
title: Finite one-cut balance contradicts vanishing-defect regular atlas microstates
target: non-hyperlinear-group
requires:
  - leavitt-regular-atlas-hyperlinearity-criterion
  - finite-tracial-one-cut-balance
  - atlas-one-cut-finite-multiplicity-extraction
artifacts:
  - notes/ATLAS_RELATIVE_PERFECTNESS_AND_COEFFICIENT_ENDPOINT.md
---

Assume the three prerequisites and suppose

```text
Q=L_(F_2)(1,2)^x
```

were hyperlinear.  The canonical regular-atlas criterion gives a sequence of
multiplicities `k_n` and relative chart unitaries whose packet defects
`delta_n` tend to zero.  Apply the extraction claim to obtain `P_n,W_n` in
finite matrix amplifications of `M_(k_n)(C)` with

```text
||(1-P_n)W_nP_n||_2^2 <= C delta_n^c,
||P_nW_n(1-P_n)||_2^2 >= c0-C delta_n^c.
```

But `finite-tracial-one-cut-balance` makes the two norms exactly equal for
every `n`.  Hence

```text
c0 <= 2 C delta_n^c,
```

which is impossible as `delta_n -> 0`.  Therefore the explicit binary Leavitt
unit group `Q` is not hyperlinear.