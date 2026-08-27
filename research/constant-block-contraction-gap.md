---
rg: 2
id: constant-block-contraction-gap
kind: claim
title: A contraction in four-by-four operator blocks is bounded away from every constant-block operator with large coefficient
artifacts:
  - notes/TRUE_TRACE_FLAT_COMMON_BLOCK_CONTRACTION_GAP.md
distinct_from:
  common-range-isometries-have-maximal-gram-overlap: that lower-bounds the Gram overlap of two partial isometries sharing a range; this lower-bounds the distance from a block contraction to the constant-block subspace and involves no partial isometries.
---

Let `(N,tau_N)` be a finite tracial von Neumann algebra and give
`M_4(N)` its normalized trace and normalized Hilbert--Schmidt norm.  For
`C in N` write

```text
K(C) = (1/2) J_4 tensor C,
```

where `J_4` is the all-ones matrix, i.e. the operator all of whose sixteen
blocks equal `C/2`.  Then for every `T=(T_ij) in M_4(N)` with
`||T||_op <= 1` and every `C in N`:

```text
||T - K(C)||_2^2 = (1/4) sum_(i,j) ||T_ij - C/2||_(2,N)^2,        (CBG1)
||T - K(C)||_2   >= ||C||_(2,N) - 1/2,                            (CBG2)
||T - K(C)||_2^2 >= max(0, ||C||_(2,N) - 1/2)^2.                  (CBG3)
```

**Pauli instance.**  If a sequence of contractions `T_n in M_4(N_n)` has all
sixteen blocks of exact mass `||T_(ij,n)||_(2,N_n)^2 = 1/8` and satisfies the
common-block coherence hypothesis

```text
(1/4) sum_(i,j) ||T_(ij,n) - C_n/2||_(2,N_n)^2 -> 0,              (CBG4)
```

then `||C_n||_2 -> 1/sqrt(2)` by `(CBG1)` and the reverse triangle inequality,
and `(CBG3)` gives

```text
liminf_n ||T_n - K(C_n)||_2^2 >= (1/sqrt(2) - 1/2)^2
                               = 3/4 - 1/sqrt(2) > 0,             (CBG5)
```

contradicting `(CBG4)`.  So no contraction sequence can be both trace-flat at
mass `1/8` per block and common-block coherent.

`(CBG1)`--`(CBG3)` are unconditional and hold in every finite tracial von
Neumann algebra.  Only `(CBG4)` is a hypothesis, and it is precisely the
remaining gate of `TRUE_TRACE_FLAT_COMMON_BLOCK_CONTRACTION_GAP.md`: sections 5
to 7 of that note reduce it to recovering four bounded finite-coordinate
row/column shifts, and section 6 proves those shifts can never be group words,
because the trace-flat packet exists in the regular representation while
`(CBG2)` holds in every finite tracial algebra.
