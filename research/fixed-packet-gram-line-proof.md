---
rg: 2
id: fixed-packet-gram-line-proof
kind: route
title: Avoid the fixed packet spectra with a diagonal Gram unitary
target: fixed-packet-orbits-cannot-amplify-a-gram-line
requires: []
---

The literal orbit of one vector under `s` fixed packet/gauge words in a
fixed space `F` has dimension at most `s dim(F)`.  In
`F tensor L^2(M_d)` its normalized projection trace is therefore at most
`s/d^2`.

For the spectral strengthening, let `T_1,...,T_s in U(F)` be arbitrary and
let `Sigma` be the union of their spectra.  Choose distinct phases
`lambda_1,...,lambda_d` recursively so that

```text
lambda_i conjugate(lambda_j) notin Sigma^(-1)  (i!=j),
```

which is possible because each step forbids finitely many values.  Put
`D_d=diag(lambda_i)` and `W_d=Ad(D_d)` on `L^2(M_d)`.  The matrix unit
`E_ij` has `W_d`-eigenvalue `lambda_i conjugate(lambda_j)`.  Hence no
off-diagonal `E_ij tensor f` is fixed by `W_d tensor T_a`; its fixed space
is contained in the diagonal subspace and has dimension at most
`d dim(F)`.  The ambient dimension is `d^2 dim(F)`, giving density at most
`1/d`.  Meanwhile `W_d(I_d)=I_d`, so the original Gram vector is fixed
exactly.  Taking the union of spectra also proves the assertion for finite
direct sums and finite gauge orbits.
