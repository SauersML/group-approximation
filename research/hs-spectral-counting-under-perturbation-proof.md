---
rg: 2
id: hs-spectral-counting-under-perturbation-proof
kind: route
title: Apply Hoffman--Wielandt to the ordered eigenvalue lists
target: hs-spectral-counting-under-perturbation
requires: []
---

Order the eigenvalues of `A,C` increasingly as `lambda_i,mu_i`.
Hoffman--Wielandt gives

```text
(1/N) sum_i |lambda_i-mu_i|^2 <= ||A-C||_2^2.
```

If the number of `lambda_i<=a` exceeds the number of `mu_i<=b` by `k`, then
for at least `k` paired indices one has `lambda_i<=a< b<mu_i`; each such pair
contributes at least `(b-a)^2`. Hence

```text
k/N <= ||A-C||_2^2/(b-a)^2,
```

which is `(HSC1)`. Interchanging the operators proves the other direction.

