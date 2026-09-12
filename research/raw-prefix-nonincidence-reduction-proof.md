---
rg: 2
id: raw-prefix-nonincidence-reduction-proof
kind: route
title: Telescope the cap prefix, coarea-select its source, and audit the minimal OR3 cycle
target: raw-prefix-covariance-reduces-to-nonincidence-cap-commutators
requires:
  - rstar-fano-caps-have-seven-maximal-parity-covers
---

For `(RPC3)`, insert and subtract
`q_cB_xq_(c-1)...q_1P`, then expand the commutator of `B_x` with the product
`q_(c-1)...q_1P`.  This gives the displayed sum with no estimate.  Taking
the adjoint of `(RPC2)` and using `[A_(c,x),q_c]=0` gives `(RPC4)`.

For the common source cut, write the eigenvalues of `H` as `lambda_i`.  In
that basis,

```text
int_0^1 ||[B,1_[t,1](H)]||_2^2 dt
 =sum_(i,j)|B_(ij)|^2 |lambda_i-lambda_j|
 <=||B||_2 ||[B,H]||_2
 =||[B,H]||_2.
```

Average the sum of these identities over `[a/4,a/2]` to obtain one threshold
working for every `B_x`.  Since `t<=a/2` and `0<=H<=1`,

```text
a<=t(1-tau(P))+tau(P)
```

implies `(RPC6)`.  Product telescoping gives `(RPC9)`.  Substitution into
`(RPC3)`, followed by the fixed finite Cauchy--Schwarz bound, proves the
vanishing-modulus conclusion.

For sharpness, use the seven-dimensional rational matrices in the artifact.
Each selected cap is the sum of four atoms of one of the parity fibres
classified by the required claim.  The script checks PVM orthogonality and
full support, all six zero incidence rows, the exact Gram spectrum, the
threshold source, and equality of the raw row with the sole nonincidence
term `(RPC13)`.  Its output is

```text
dimension=7 (minimal for a full-support seven-atom OR3 PVM)
cap_ranks=4,4,4
all_six_incidence_rows_hs2=0
sequential_mass_a=3/14
gram_spectrum=1,1/2,0,0,0,0,0
threshold=a/2=3/28; source_rank=2
raw_prefix_covariance_hs2=1/7
nonincidence_commutator_term_hs2=1/7
```

