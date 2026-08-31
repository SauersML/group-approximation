---
rg: 2
id: exterior-power-and-determinant-blindness-proof
kind: proof
title: Compute the balanced exterior characters and their Hilbert--Schmidt Lipschitz loss
target: jacobson-head-evades-determinant-and-fixed-exterior-power
requires: []
---

Put `d=2m`. The characteristic generating polynomial of the
eigenvalue multiset of `W_d` is

```text
product_(i=1)^d (1+lambda_i t)
  =(1+t)^m(1-t)^m
  =(1-t^2)^m.                                           (JED2)
```

The trace of the `k`-th exterior power is the `k`-th elementary
symmetric polynomial in the eigenvalues. Dividing the coefficient of
`t^k` in `(JED2)` by `binom(2m,k)` gives exactly

```text
tr(exterior^k W_d)
  =0                                              for odd k,
  =(-1)^j binom(m,j)/binom(2m,2j)                 for k=2j.
                                                               (JED3)
```

For fixed `j>=1`, the numerator has degree `j` in `m` and the
denominator has degree `2j`, so the ratio tends to zero. The ordinary
determinant is `(-1)^m`; replacing every microstate by its direct sum
with itself makes the negative multiplicity even, changes no normalized
trace or normalized Hilbert--Schmidt defect, and makes the determinant
one. In a finite tracial von Neumann algebra the Fuglede--Kadison
determinant of every unitary is one, since `log |W_d|=0`.

It remains to verify that exterior powers do not secretly improve the
defect. Let `U,V in U(d)`, diagonalize `U^*V`, and denote its
eigenvalues by `z_1,...,z_d`. For each `k`-element subset `A`,

```text
|product_(i in A) z_i-1|^2
 <= k sum_(i in A) |z_i-1|^2.                           (JED4)
```

Indeed, telescope the product and apply Cauchy--Schwarz. Average
`(JED4)` over all `k`-element subsets. Each index occurs in the
fraction `k/d` of them, so

```text
||exterior^k U-exterior^k V||_2^2
 <= k^2 (1/d) sum_i |z_i-1|^2
 = k^2 ||U-V||_2^2.                                    (JED5)
```

This proves `(JED1)`. Because exterior power is an actual group
homomorphism, word evaluation commutes with it. Thus a presentation
relator with defect at most `epsilon` has exterior-power defect at
most `k epsilon`.

Now suppose a sequence of matrix microstates has a head involution
whose normalized character tends to zero. For every fixed `k`, direct
sum stabilization leaves its spectral imbalance at `o(d)`; changing
that `o(d)) corner to an exactly balanced involution changes every
fixed exterior character by `o(1)`. Formula `(JED3)` then shows that
the exterior head character still tends to zero, while `(JED5)`
preserves all relators asymptotically.

If `k=k(d)` grows, `(JED5)` requires the unprovided rate

```text
k(d) epsilon_d -> 0.
```

At the extreme degree `k=d`, exterior power is precisely the already
blind determinant and the Lipschitz loss is of order `d`. Hence no
dimension-free head modulus follows from this family of invariants.
