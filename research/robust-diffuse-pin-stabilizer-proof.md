---
rg: 2
id: robust-diffuse-pin-stabilizer-proof
kind: route
title: Spectrally block an approximate stabilizer and polar-correct its diagonal blocks
target: robust-diffuse-pin-stabilizer-has-zero-entropy
requires: []
---

Fix an integer `q` and a small number `tau>0`.  Choose `q-1` cut points of
the atomless limiting spectral measure and then disjoint boundary intervals
around them of total mass below `tau`.  For all large `n`, functional
calculus gives a decomposition

```text
1=Q_(0,n)+Q_(1,n)+...+Q_(q,n)                            (RDP3)
```

such that `rank(Q_(0,n))/d_n<=2tau`, each core block has normalized rank at
most `1/q+2tau`, and distinct core spectra are separated by one fixed
`gamma>0`.

If `U in Z_n(eta_n)`, the Sylvester estimate on two separated spectral
blocks gives

```text
||Q_(i,n) U Q_(j,n)||_2 <= eta_n/gamma   (i,j>=1,i!=j).  (RDP4)
```

All matrix entries meeting `Q_(0,n)` have total normalized HS norm at most
`2 sqrt(2tau)`.  Hence `U` is within
`o_n(1)+O_q(sqrt(tau))` of its block diagonal compression.  The latter is
an almost unitary on every block; blockwise polar decomposition changes it
by the same order and produces an element of

```text
U(rank Q_(0,n)) x product_(j=1)^q U(rank Q_(j,n)).       (RDP5)
```

A volumetric unitary-group net therefore has logarithmic exponent at most

```text
log(C/epsilon) [rank(Q_(0,n))^2+sum_j rank(Q_(j,n))^2]. (RDP6)
```

After division by `d_n^2`, the limsup is bounded by

```text
log(C/epsilon) [(2tau)^2+q(1/q+2tau)^2].                (RDP7)
```

First let `n` tend to infinity, then `tau` tend to zero, and finally
`q` tend to infinity.  This proves `(RDP1)`.  Conjugation of an `F`-tuple
bounded by `R` is `2R sqrt(|F|)`-Lipschitz in normalized HS norm, so pushing
the stabilizer net through the orbit map proves `(RDP2)`.
