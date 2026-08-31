---
rg: 2
id: stw83-star-homomorphic-carrier-leakage-proof
kind: route
title: Use constant fibre representation type and a positive block-matrix estimate
target: stw83-star-homomorphic-plateau-carriers-have-norm-one-leakage
requires:
  - stw83-compressed-one-colour-carries-circle-matrix-finite-sets
---

Put `y=pi(b)`.  We first note that

```text
norm(y(t)) is independent of t in T.                    (3)
```

Indeed, write `F=direct-sum_l M_(n_l)`.  For each central unit
`z_l in F`, the function `t |-> pi_t(z_l)` is a continuous
projection-valued function.  Its rank is integer valued and hence constant
on the connected circle.  Thus the multiplicity with which each matrix
summand occurs in the finite-dimensional representation `pi_t` is
independent of `t`.  The spectrum, and in particular the norm, of
`pi_t(b)` is therefore constant.

At `t_+`, (1) gives

```text
norm(p y(t_+) p)>=1-epsilon.
```

Hence `norm(y(t_+))>=1-epsilon`, and (3) gives

```text
norm(y(t_-))>=1-epsilon.                                (4)
```

At `t_-`, equation (1) instead gives

```text
norm(p y(t_-) p)<epsilon.                               (5)
```

Write the positive contraction `y(t_-)` in `p+q` block form.  Set

```text
a=norm(p y(t_-) p),       d=norm(q y(t_-) q).
```

Positivity of the block matrix gives the standard estimate

```text
norm(p y(t_-) q)<=sqrt(a d).                            (6)
```

For example, (6) follows by writing the off-diagonal block as the product
of the corresponding row and column of `y(t_-)^(1/2)`.  The triangle
inequality for the four blocks, followed by (5)--(6), yields

```text
norm(y(t_-))
 <=a+d+2sqrt(a d)
 <epsilon+d+2sqrt(epsilon d)
 =(sqrt(epsilon)+sqrt(d))^2.                            (7)
```

Combining (4) and (7), and using `epsilon<1/2`, gives

```text
sqrt(d)>=sqrt(1-epsilon)-sqrt(epsilon).
```

Squaring proves (2).

For a nonconstant positive coefficient cutoff, the lower bound approaches
one.  Since every completely positive return of that positive input is
positive, another colour cannot cancel this complementary block.  A usable
moving carrier must instead replace the unital homomorphism by an order-zero
map with a phase-dependent support that dies before the target cutoff does;
making that taper coexist with the scalar Toeplitz transition is exactly the
remaining buffer problem.
