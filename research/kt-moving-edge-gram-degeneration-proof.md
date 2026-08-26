---
rg: 2
id: kt-moving-edge-gram-degeneration-proof
kind: route
title: Hide one moving edge word in a dominant quotient block
target: kt-kazhdan-edge-grams-are-conditioned-only-at-fixed-radius
requires:
  - kt-pair-group-double-is-nonsofic
---

For the fixed-window assertion, every diagonal entry of `(KGC1)` is one.
If the off-diagonal entries have modulus at most `epsilon`, Gershgorin's
theorem gives `(KGC2)`.  Pointwise convergence to the regular character
makes `epsilon->0` for fixed `F`.

For the moving calibration, exhaust the nonidentity elements of `G` by
finite sets `F_n`.  Residual finiteness gives a finite quotient

```text
q_n:G->Q_n
```

which kills none of `F_n`.  Since `Gamma` is infinite and `Q_n` is finite,
choose

```text
1!=k_n in Gamma intersection ker(q_n).                  (KGP1)
```

Residual finiteness again gives a finite quotient

```text
r_n:G->R_n,             r_n(k_n)!=1.                   (KGP2)
```

Let `lambda_Q` and `lambda_R` be the finite left regular representations and
put

```text
rho_n=(lambda_(Q_n) o q_n)^(direct sum M_n)
          direct_sum (lambda_(R_n) o r_n).              (KGP3)
```

Choose `M_n` so large that the normalized dimension of the last block,

```text
alpha_n=|R_n|/(M_n|Q_n|+|R_n|),                         (KGP4)
```

is at most `a_n`.  The normalized character is

```text
chi_n(g)
 =(1-alpha_n) 1_[q_n(g)=1]+alpha_n 1_[r_n(g)=1].        (KGP5)
```

For every fixed `g!=1`, eventually `g in F_n`, so the first indicator
vanishes and `|chi_n(g)|<=alpha_n->0`.  Thus `(rho_n)` has canonical limiting
character.

But `(KGP1)--(KGP2)` give

```text
chi_n(k_n)=1-alpha_n.                                   (KGP6)
```

Hence the Gram matrix of `1,rho_n(k_n)` is

```text
[[1,1-alpha_n],[1-alpha_n,1]],                          (KGP7)
```

whose least eigenvalue is `alpha_n<=a_n`.  The two matrices are linearly
independent because their restrictions to the `R_n` block differ.  Since
the group image linearly spans its finite-dimensional group algebra, extend
them to a group-image basis of `C*(rho_n(Gamma))`.  The two-by-two matrix in
`(KGP7)` is a principal submatrix of the full Gram, so eigenvalue
interlacing keeps the full least eigenvalue at most `alpha_n`.

The construction is exact and works despite property `(T)` of `Gamma`; the
ill-conditioned word necessarily moves beyond every fixed window.
