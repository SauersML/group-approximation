---
rg: 2
id: arithmetic-leak-has-sparse-heat-capture
kind: claim
title: Every arithmetic projective leak is captured by an asymptotically null sparse heat cutoff
distinct_from:
  arithmetic-leak-has-fd-null-laplacian-witness: that supplies one fixed-depth finite-dimensional-null detector sequence; this diagonalizes the heat depth along a canonical matrix enemy and proves that the detector has vanishing normalized superoperator rank while retaining constant mass on the selected inner automorphism.
  arithmetic-selected-fd-null-cutoff-cannot-survive-matrices: that asks to kill the selected value and would prove transfer; this proves the sharp unconditional alternative that any surviving selected value is concentrated in a vanishing-density singular subspace.
  adjoint-supertrace-cannot-pay-hs-selection-load: that gives a generic one-dimensional counterexample to a supertrace-to-selected-vector inference; this derives the sparse subspace canonically from the arithmetic Kazhdan heat filters of every projective-transfer enemy.
---

Put

```text
C=SL_3(Z) < A=SL_3(Z[1/p]),
h=diag(p,1,1/p).
```

Let `rho_j` be canonical-character normalized-Hilbert--Schmidt asymptotic
matrix representations of `A`, and let `U_j` be unitaries such that

```text
sum_(c in S_C) (1-|tr([U_j,rho_j(c)])|^2) -> 0,
liminf_j (1-|tr([U_j,rho_j(h)])|^2) >= epsilon > 0.       (SHC1)
```

On the normalized Hilbert spaces

```text
H_j=End(M_(d_j)),
beta_j(g)=Ad(rho_j(g)),
gamma_j(g)=Ad(beta_j(g)),
T_j=Ad(U_j) in H_j,                                      (SHC2)
```

there are, after passing to a subsequence, integers `N_j->infinity` and
operators

```text
A_j=gamma_j((h-1)x_(N_j)),
x_N=(1-Delta_C/L)^N,
Delta_C=sum_(c in S_C)(1-c)^*(1-c),  L=4|S_C|,            (SHC3)
```

such that

```text
||A_j||_(2,B(H_j)) -> 0,
liminf_j ||A_j T_j||_(2,H_j) >= sqrt(2 epsilon).           (SHC4)
```

Here `(SHC3)` means the literal evaluated polynomial

```text
A_j=(gamma_j(h)-I)
    (I-gamma_j(Delta_C)/L)^(N_j),                          (SHC5)
```

so no multiplicativity at a depth depending on `j` is being assumed.

More quantitatively, put `alpha=sqrt(epsilon/2)` and let

```text
P_j=1_[alpha,infinity)(|A_j|) in B(H_j).                  (SHC6)
```

Then

```text
rank(P_j)/dim(H_j) -> 0,
liminf_j ||P_j T_j||_(2,H_j) >= sqrt(2 epsilon)/4.         (SHC7)
```

Thus every counterexample to the dimension-free trace-square modulus
forces a full-rank inner automorphism to place fixed Hilbert mass in a
vanishing-density singular subspace selected by the arithmetic heat
cutoff.  Robust spectral gap or normalized supertrace decay alone cannot
exclude the enemy: the remaining statement must control this selected
inner vector, not merely the density of the exceptional spectrum.

DERIVATION
`arithmetic-sparse-heat-capture-proof`
