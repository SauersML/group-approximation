---
rg: 2
id: projective-fixed-carrier-fejer-bound-proof
kind: route
title: Twist away the varying phase and apply the finite Fejer polynomial
target: canonical-moments-bound-projective-fixed-carrier-density
requires: []
---

Put

```text
U_n=conjugate(lambda_n)V_n,
epsilon_n=||(U_n-1)X_n||_2,
alpha_n=||X_n||_2^2.                                    (PFB1)
```

The phases do not change moment magnitudes:

```text
|tr(U_n^k)|=|tr(V_n^k)|.                                (PFB2)
```

For

```text
B_N(z)=sum_(j=0)^(N-1)z^j,
F_N(z)=N^(-1)B_N(z)^*B_N(z),                            (PFB3)
```

the telescoping argument gives

```text
tr(F_N(U_n))
 >= N(sqrt(alpha_n)-(N-1)epsilon_n/2)_+^2.              (PFB4)
```

Expanding the same polynomial and using `(PFB2)` gives, with
`eta_n=max_(0<|k|<N)|tr(V_n^k)|`,

```text
tr(F_N(U_n)) <= 1+(N-1)eta_n.                           (PFB5)
```

Here `epsilon_n,eta_n->0`.  Combining `(PFB4)--(PFB5)` and taking the upper
limit yields

```text
N limsup_n alpha_n <=1,
```

which is `(PFC3)`.  The regular `C_N` example in `(PFC4)` has equality in
the limiting bound, proving sharpness.
