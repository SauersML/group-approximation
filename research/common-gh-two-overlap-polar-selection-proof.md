---
rg: 2
id: common-gh-two-overlap-polar-selection-proof
kind: route
title: Average one isometry over each overlap and compare the two polar parts
target: common-gh-isometry-selects-the-two-overlap-cross-coefficient
requires:
  - gowers-hatami-finite-group-hs-stability
  - summed-reynolds-carrier-transports-only-tautologically
---

For `i in {1,3}` define the averaged intertwiner

```text
T_i=|H_i|^(-1) sum_(h in H_i)
 beta_i(h)V alpha_i(h)^*.                               (CGI7)
```

Reindexing the sum shows

```text
beta_i(k)T_i=T_i alpha_i(k)       for every k in H_i.   (CGI8)
```

By the triangle inequality followed by Cauchy--Schwarz and `(CGI1)`,

```text
||T_i-V||_F<=eta_i sqrt(d).                              (CGI9)
```

Write the polar decomposition `T_i=U_i|T_i|`.  Since `(CGI8)` holds,
`|T_i|` commutes with `alpha_i(H_i)` and the polar part intertwines on its
initial support.  Let

```text
p_i=1_[1/2,infinity)(|T_i|).
```

It is `alpha_i(H_i)`-invariant.  Mirsky's singular-value inequality, applied
to `T_i` and the isometry `V` whose `d` singular values are all one, gives

```text
sum_j (s_j(T_i)-1)^2<=||T_i-V||_F^2<=eta_i^2 d.         (CGI10)
```

Every singular value below `1/2` contributes more than `1/4`; hence the
rank bound in `(CGI2)`.  On `p_i`, `(CGI9)` and `(CGI10)` give

```text
||U_i p_i-Vp_i||_F
 <=||(U_i-T_i)p_i||_F+||(T_i-V)p_i||_F
 <=2eta_i sqrt(d),
```

which completes `(CGI2)`.

The codimension of an intersection of two subspaces is at most the sum of
their codimensions, proving `(CGI3)`.  On `p<=p_1,p_3`, use
`U_i^*U_i p=p` to obtain

```text
||(U_3^*U_1-I)p||_F
 <=||(U_1-V)p||_F+||U_3^*(V-U_3)p||_F
 <=2(eta_1+eta_3)sqrt(d),
```

which is `(CGI4)`.  Compression is Frobenius-contractive, so the triangle
inequality with `||tilde B-I||_2<=epsilon` proves `(CGI5)`.  Equation
`(CGI6)` is immediate from `Q^*Q=I`.

Finally, invariance of `p_i` is only invariance under its own `H_i`.
Intersections of invariant subspaces for two different groups need not be
invariant for either, and Frobenius-smallness does not create a literal
kernel.  Explicitly, `(CGI12)` has normalized-HS distance
`|e^(it_d)-1|` from the identity but has no nonzero identity restriction for
any `t_d!=0`.  Therefore the construction selects the cross coefficient but
does not manufacture an exact simultaneous intertwiner, even after deleting
any subspace while retaining nonzero dimension.
