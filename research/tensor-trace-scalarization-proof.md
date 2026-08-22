---
rg: 2
id: tensor-trace-scalarization-proof
kind: route
title: Compare the tensor trace product with the sum of scalar trace deficits
target: tensor-products-cannot-cancel-noncentral-hs-defect
requires: []
---

Write `a_f=|tau_f(U_f)|`, `x=1-prod_f a_f`, and
`S=sum_f(1-a_f)`.  Since

```text
prod_f a_f <= exp(-S),
```

we have `S<=-log(1-x)`.  The hypothesis
`||U-I||_2^2<=1` implies

```text
2x=d_tensor^2<=||U-I||_2^2<=1,
```

so `x<=1/2` and `-log(1-x)<=2x`.  Therefore

```text
sum_f d_f^2=2S<=4x=2d_tensor^2,
```

which proves `(TSC2)`.  Equality in the scalar target case gives `x=0`,
hence every `a_f=1`; a unitary has trace of modulus one only when it is the
corresponding scalar in `L_2`.

For `(TSC3)`, normalized tensor traces factor and left multiplication by
`(tensor_f Q_i^(f)Q_j^(f))^*` preserves the `L_2` norm, giving the stated
commutator identity.
