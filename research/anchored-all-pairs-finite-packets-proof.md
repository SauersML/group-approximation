---
rg: 2
id: anchored-all-pairs-finite-packets-proof
kind: route
title: Apply Gowers--Hatami and then the anchored flexible-compression theorem
target: anchored-all-pairs-finite-packets-have-zero-entropy
requires:
  - gowers-hatami-finite-group-hs-stability
  - anchored-flexible-compressions-have-zero-entropy
---

For all large `n`, `epsilon_n<1/16`.  Apply
`gowers-hatami-finite-group-hs-stability` to each `f in Phi_n`.  It gives an
exact representation `rho:G_n->U(m)`, with `m` in `(AFP7)`, and an isometry
`V:C^(d_n)->C^m` such that

```text
max_(g in G_n)||f(g)-V^*rho(g)V||_2<=42epsilon_n.        (APP1)
```

The padding satisfies

```text
0<=m-d_n<=[4epsilon_n^2/(1-4epsilon_n^2)]d_n=o(d_n).    (APP2)
```

For the exact pin

```text
A_rho=sum_(g in L_n)c_(g,n)rho(g),
```

`(APP1)` and the uniform coefficient `l1` bound give

```text
||V^*A_rho V-D_n||_2<=42C epsilon_n->0.                 (APP3)
```

Pad all exact representations to the largest permitted dimension by adding
trivial summands; this changes the padding by only `o(d_n)` and multiplies
the exact class count by at most the number of dimensions in `(AFP7)`, whose
logarithm is `o(d_n^2)`.  The family of exact output tuples and pins therefore
satisfies `anchored-flexible-compressions-have-zero-entropy`.

Finally `(APP1)` places every approximate output tuple in a
`42epsilon_n sqrt(|F_n|)`-neighbourhood of that entropy-null family.  The
coordinate count is uniformly bounded and this radius tends to zero, so its
fixed-precision covering exponent is also zero, proving `(AFP8)`.
