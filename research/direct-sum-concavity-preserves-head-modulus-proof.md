---
rg: 2
id: direct-sum-concavity-preserves-head-modulus-proof
kind: proof
title: Concavity makes the bounded-dimension head modulus stable under arbitrary direct sums
target: bounded-block-jacobson-microstates-also-collapse
requires:
  - bounded-dimension-jacobson-head-has-algebraic-collapse
---

Let `C_D,alpha_D` be the constants in `(BDJ2)` and put

```text
beta_D=min(alpha_D,1),             K_D=max(C_D,2).       (DSP1)
```

Consider one irreducible block `U_j` of size at most `D), and define

```text
delta_j=max_(r in R)||r(U_j)-I||_(2,j),
h_j=||w(U_j)-I||_(2,j).
```

If `delta_j<=1`, then `(BDJ2)` and `beta_D<=alpha_D` give

```text
h_j<=C_D delta_j^alpha_D<=K_D delta_j^beta_D.
```

If `delta_j>1`, the trivial unitary bound `h_j<=2` gives the same
inequality. Hence, for every small block,

```text
h_j^2<=K_D^2 (delta_j^2)^beta_D.                         (DSP2)
```

Write `lambda_j` for the normalized dimension weight of block `j`,
including its multiplicity. Let `S_D` be the small blocks and put

```text
p=sum_(j in S_D)lambda_j<=1.
```

For `0<beta_D<=1`, concavity of `x |-> x^beta_D` gives

```text
sum_(j in S_D) lambda_j (delta_j^2)^beta_D
 <= p^(1-beta_D)
    (sum_(j in S_D)lambda_j delta_j^2)^beta_D
 <= (sum_(j in S_D)lambda_j delta_j^2)^beta_D.          (DSP3)
```

If `d_(r,j)=||r(U_j)-I||_(2,j)`, then

```text
delta_j^2=max_(r in R)d_(r,j)^2
             <=sum_(r in R)d_(r,j)^2.
```

Word evaluation is block diagonal, so

```text
sum_j lambda_j d_(r,j)^2=||r(U)-I||_2^2.
```

It follows that

```text
sum_(j in S_D)lambda_j delta_j^2
 <=sum_(r in R)||r(U)-I||_2^2
 <=|R| delta(U)^2.                                      (DSP4)
```

Combining `(DSP2)--(DSP4)`, the small-block contribution to the
squared head defect is at most

```text
K_D^2 |R|^beta_D delta(U)^(2 beta_D).                   (DSP5)
```

On every large block the trivial head bound is `h_j^2<=4`. Their total
contribution is therefore at most `4mu_D(U)`. Adding it to `(DSP5)`
proves `(BBJ1)`.

Finally, if the full head defect is at least `epsilon` and
`delta(U_k)->0`, then `(BBJ1)` gives

```text
epsilon^2
 <=o(1)+4mu_D(U_k).
```

Taking the lower limit proves `(BBJ2)` for every fixed `D`.

The argument uses the irreducible decomposition only to obtain blocks of
bounded size. Repeated multiplicities cause no loss because normalized
Hilbert--Schmidt squares add with the weights `lambda_j`. Thus direct
sums of any number of finite complementary-sign packet representations
remain on the collapsing side of the firewall.
