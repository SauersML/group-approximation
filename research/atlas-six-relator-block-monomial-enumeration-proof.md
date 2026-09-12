---
rg: 2
id: atlas-six-relator-block-monomial-enumeration-proof
kind: route
title: Enumerate the atomic GL4(2) alignments and add ranks
target: atlas-six-relator-block-monomial-rank-gap
requires: []
artifacts:
  - experiments/atlas_six_relator_block_monomial_verify.js
  - experiments/atlas-six-relator-block-monomial-rank-gap.json
---

Write a block-monomial frame as `F=P_sigma D`, where `P_sigma` permutes the
`k` four-dimensional summands and
`D=diag(A_1,...,A_k)` with `A_i in GL_4(2)`.  Since every diagonal block of
`rho_k(g)` is the same, `P_sigma` commutes with `rho_k(g)`.  This remains
true for every cycle of `sigma`, not only for fixed block labels.  Hence

```text
F^(-1) rho_k(g) F
 =D^(-1) P_sigma^(-1) rho_k(g) P_sigma D
 =diag(A_i^(-1) rho(g) A_i)_i.                         (BME1)
```

Every six-relator value is therefore block diagonal.  For each word `w`,

```text
rank(pi_F(w)-I)=sum_i rank(pi_(A_i)(w)-I_4).           (BME2)
```

It remains only to prove the atomic inequality.  The verifier scans the
`65536` row-packed binary matrices in increasing packed order.  Exact
Gaussian elimination accepts `20160` matrices, as required by

```text
|GL_4(2)|=(16-1)(16-2)(16-4)(16-8)=20160.
```

For every accepted `A` it forms `A^(-1)rho(g)A` for each factor-two letter,
multiplies the six stored syllable lists, and computes six residual ranks by
binary elimination.  The asserted histogram has minimum `1` and unique
minimum at `A=I_4`.  Summing that atomic floor through (BME2) proves (BMR1).

If equality holds, every atomic summand must be the unique minimizer, so all
`A_i=I_4` and `F=P_sigma`.  Conversely every pure summand permutation
commutes with the chart; direct replay gives five zero boundary residuals and
collision rank one per summand.  Thus equality is sharp and its minimizers
are exactly as stated.  The same argument shows explicitly why permutation
cycles cannot couple or cancel residual ranks: after (BME1) no off-diagonal
block survives on which such cancellation could occur.
