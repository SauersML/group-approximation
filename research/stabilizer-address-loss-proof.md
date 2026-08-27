---
rg: 2
id: stabilizer-address-loss-proof
kind: route
title: Telescope stabilizer conjugations and exhibit the two-dimensional sharpness family
target: stabilizer-generator-control-has-unbounded-address-loss
requires: []
---

For `(SGL1)`, cancel the common outer conjugation by `U_g`.  For `(SGL2)`,
write `h=t_1...t_L`, compare the successive conjugates

```text
A, Ad(U_(t_1))(A), ..., Ad(U_(t_1...t_L))(A),
```

and use the triangle inequality.  Each increment is a unitary conjugate of
`A-Ad(U_(t_i))(A)`, so normalized Hilbert--Schmidt invariance gives the stated
sum.

For sharpness, conjugation by `exp(i theta sigma_x/2)` rotates the Bloch vector
of `sigma_z` through angle `theta`.  Since the normalized Hilbert--Schmidt
inner product of Pauli matrices is their Euclidean Bloch inner product,

```text
||sigma_z-Ad(U_(t^n))(sigma_z)||_2^2
 =2-2 cos(n theta)=4 sin^2(n theta/2).
```

Set `n=L` and `theta=L^-2`.  The quotient of the `n=L` defect by the generator
defect is

```text
sin(1/(2L))/sin(1/(2L^2)),
```

which tends to `L`.  Hence no address-independent Lipschitz constant follows
from the finite generator estimates.
