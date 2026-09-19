---
rg: 2
id: arithmetic-sparse-heat-capture-proof
kind: route
title: Diagonalize the arithmetic heat depth and cut its high singular subspace
target: arithmetic-leak-has-sparse-heat-capture
requires: []
---

We use normalized Hilbert--Schmidt norms throughout.  For a fixed `j`, the
operators `gamma_j(c)` are unitaries on `H_j`.  Consequently

```text
0 <= gamma_j(Delta_C) <= L I,
R_j=I-gamma_j(Delta_C)/L
```

is a positive contraction.  In particular

```text
||A_j||_op=||(gamma_j(h)-I)R_j^(N_j)||_op <=2.             (SHP1)
```

We first obtain normalized superoperator decay.  The restriction of the
left regular representation `lambda_A` to `C` is a direct sum of copies of
`lambda_C`.  Property `(T)` (in fact nonamenability is enough here) gives a
number `kappa>0` such that

```text
lambda_A(Delta_C) >= kappa I.
```

After decreasing `kappa` if necessary, spectral calculus gives

```text
||lambda_A(x_N)||_op <=q^N,
||lambda_A((h-1)x_N)||_op <=2q^N,
q=1-kappa/L<1.                                           (SHP2)
```

The canonical character passes through both adjoints:

```text
tr(beta_j(g))=|tr(rho_j(g))|^2,
tr(gamma_j(g))=|tr(rho_j(g))|^4 -> 1_(g=e).              (SHP3)
```

Because `rho_j` is an asymptotic representation, the same holds for every
fixed group-ring `*`-moment.  Hence, for every fixed `N`,

```text
lim_j ||(gamma_j(h)-I)R_j^N||_(2,B(H_j))
 =||lambda_A((h-1)x_N)||_2
 <=2q^N.                                                 (SHP4)
```

We next retain the selected value.  Direct computation of the twice-adjoint
action gives, for every fixed `c`,

```text
||gamma_j(c)T_j-T_j||_2^2
 =2(1-|tr([U_j,rho_j(c)])|^2).                           (SHP5)
```

Thus `(SHC1)` implies, for every fixed `N`,

```text
||R_j^N T_j-T_j||_2 ->0.                                (SHP6)
```

Choose an increasing subsequence diagonally so slowly that `N_j->infinity`
and both

```text
||A_j||_2 <=2q^(N_j)+1/N_j,
||R_j^(N_j)T_j-T_j||_2 <=1/N_j                           (SHP7)
```

hold.  This uses only the fixed-`N` limits `(SHP4)` and `(SHP6)`; it does
not evaluate any asymptotic multiplicativity estimate at a preassigned
growing word length.  The first line of `(SHP7)` proves the first part of
`(SHC4)`.  The second and `(SHP1)` imply

```text
||A_jT_j-(gamma_j(h)-I)T_j||_2 <=2/N_j.                  (SHP8)
```

Another direct twice-adjoint trace calculation gives

```text
||(gamma_j(h)-I)T_j||_2^2
 =2(1-|tr([U_j,rho_j(h)])|^2).                           (SHP9)
```

Equations `(SHC1)`, `(SHP8)`, and `(SHP9)` prove the selected lower bound
in `(SHC4)`.

It remains to make sparsity explicit.  Chebyshev's inequality for the
singular-value distribution gives

```text
rank(P_j)/dim(H_j)
 <=alpha^(-2)||A_j||_(2,B(H_j))^2 ->0.                  (SHP10)
```

Moreover `||A_j(I-P_j)||_op<=alpha`, while `(SHP1)` gives
`||A_jP_j||_op<=2`.  Since `||T_j||_2=1`,

```text
||A_jT_j||_2 <=2||P_jT_j||_2+alpha.                     (SHP11)
```

Take lower limits, use `(SHC4)`, and substitute
`alpha=sqrt(epsilon/2)=sqrt(2 epsilon)/2`.  This yields

```text
liminf_j ||P_jT_j||_2
 >=(sqrt(2 epsilon)-alpha)/2
 =sqrt(2 epsilon)/4,                                    (SHP12)
```

which is `(SHC7)` and completes the proof.
