---
rg: 2
id: periodic-higman-clock-centralizer-has-linear-width-proof
kind: route
title: Sum the gcds of the nested 3-power cycle lengths
target: periodic-higman-clock-centralizer-has-linear-width
requires: []
---

The nonzero residues of additive order `3^m` form one orbit under
multiplication by `2`: its length is

```text
phi(3^m)=2*3^(m-1)=L_m.
```

Together with the fixed residue zero this gives `(HCW1)`.

The intertwiner space between cyclic permutation representations of lengths
`r` and `s` has complex dimension `gcd(r,s)`: after Fourier diagonalization,
this is the number of common eigenvalues.  Therefore the commutant dimension
of the direct sum of the cycles `(L_0,...,L_n)` is

```text
sum_(a,b=0)^n gcd(L_a,L_b).
```

The lengths are nested by divisibility.  Hence the gcd is the smaller
length, and grouping by the smaller index gives

```text
sum_(a=0)^n (1+2(n-a))L_a
 = (2n+1)+2 sum_(k=0)^(n-1) (1+2k)3^(n-k-1).          (1)
```

The finite geometric sums give

```text
sum_(k=0)^(n-1) (1+2k)/3^k
 = 3-(n+1)3^(1-n).                                   (2)
```

Substitution in `(1)` yields

```text
(2n+1)+(2*3^(n-1))(3-(n+1)3^(1-n))
 =2*3^n-1=2q-1,
```

proving `(HCW2)`.  For a finite-dimensional C-star algebra
`directSum_lambda M_(m_lambda)(C)`, the real dimension of its unitary group
is `sum_lambda m_lambda^2`, the same number as its complex vector-space
dimension, so the unitary-centralizer statement follows.

The eigenvalue `1` occurs once in every cycle, including the fixed cycle, so
its multiplicity is `n+1`.  Every other eigenvalue occurs in no more cycles,
proving maximality.  Since `L_(n-1)` divides `L_n`, the eigenvalues of the
largest cycle which occurred at an earlier level are exactly the
`L_(n-1)`-th roots.  The other `L_n-L_(n-1)=4*3^(n-2)` eigenvalues occur only
in the largest cycle and are simple, proving `(HCW3)`.

Finally `D` has the `q` distinct `q`-th roots as its spectrum, so its
commutant is the diagonal algebra and its unitary centralizer is a `q`-torus.
The parameter count in `(HCW4)` follows.  Since a dimension count cannot
exclude exceptional solutions of a nonlinear equation, no stronger claim
about `(HCW5)` is made.
