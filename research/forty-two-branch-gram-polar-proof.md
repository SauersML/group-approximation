---
rg: 2
id: forty-two-branch-gram-polar-proof
kind: route
title: Polar-round the block-column synthesis map of the branch projections
target: forty-two-branch-gram-polar-rounding
requires: []
---

For each `i`, choose an isometry

```text
J_i:C^(r_i)->C^d,       J_i J_i^*=P_i,
```

where `r_i=rank(P_i)`.  Put `K=directSum_i C^(r_i)` and form the block-column
synthesis map

```text
V:K->C^d,       V|_(C^(r_i))=J_i.                       (FGP-P1)
```

Its Gram matrix has identity diagonal blocks and off-diagonal blocks
`J_i^*J_j`.  Therefore, with unnormalized Frobenius norm,

```text
||V^*V-I_K||_F^2
 =sum_(i!=j)||J_i^*J_j||_F^2
 =sum_(i!=j) Tr(P_iP_j)
 =d Omega.                                               (FGP-P2)
```

Because `dim K<=d`, take a singular-value decomposition of `V` and replace
every singular value `sigma` by `1`, completing the zero singular vectors
inside `C^d` if necessary.  This gives an isometry `U:K->C^d`.  Since

```text
(sigma-1)^2 <=(sigma^2-1)^2       for every sigma>=0,
```

one has

```text
||V-U||_F^2<=||V^*V-I_K||_F^2.                           (FGP-P3)
```

Write `U_i` for the restriction of `U` to the `i`th summand and set

```text
E_i=U_i U_i^*.                                          (FGP-P4)
```

The `U_i` have mutually orthogonal ranges, so the `E_i` form a partial PVM
and retain the ranks `r_i`.  For each block,

```text
||J_iJ_i^*-U_iU_i^*||_F
 <=2||J_i-U_i||_F.                                      (FGP-P5)
```

Squaring, summing, dividing by `d`, and using `(FGP-P2)--(FGP-P3)` proves
`(FGP3)`.

For covariance, put `delta_i=||E_i-P_i||_(2,d)`.  The triangle inequality
and unitary invariance give

```text
||W_sE_iW_s^*-E_(s.i)||_2
 <=delta_i+||W_sP_iW_s^*-P_(s.i)||_2+delta_(s.i).        (FGP-P6)
```

Use `(x+y+z)^2<=3(x^2+y^2+z^2)`, sum over labels and average over `s`.
Every `s` permutes the labels, so the first and third sums both equal
`sum_i delta_i^2`.  Hence

```text
E_round<=3E_raw+6 sum_i delta_i^2
       <=3E_raw+24 Omega,                               (FGP-P7)
```

which is `(FGP5)`.
