---
rg: 2
id: qutrit-router-double-coset-scalar-proof
kind: route
title: Fourier-diagonalize every translate of one router double coset
target: qutrit-same-double-coset-interference-cannot-expand-carrier
requires:
  - qutrit-external-cyclic-router-selects-only-one-hidden-third
---

For a character idempotent of the abelian group `C` one has

```text
c p_a=p_a c=chi_a(c)p_a             for every c in C.  (QDS2)
```

Therefore each summand of `X` satisfies

```text
p_b(l_i U r_i)p_a
 =chi_b(l_i)chi_a(r_i)p_b U p_a.
```

Summing gives `(QDS1)`. This calculation is exact and makes no
orthogonality or generic-coefficient assumption.

The cyclic-router table says `p_bUp_a=0` unless `b=2`. In the surviving
row write

```text
p_2Xp_a=alpha_a Y_a,        Y_a=p_2Up_a.
```

If `alpha_a=0` the block has been canceled. If `alpha_a!=0`, then

```text
(p_2Xp_a)^*(p_2Xp_a)=|alpha_a|^2 Y_a^*Y_a,
(p_2Xp_a)(p_2Xp_a)^*=|alpha_a|^2 Y_aY_a^*.
```

The two support projections are therefore independent of the coefficients.
Since `Y_a` is already a partial isometry, the polar partial isometry of
the surviving block is

```text
(alpha_a/|alpha_a|)Y_a.                                (QDS3)
```

In particular, multiplying a block by `sqrt(3)` can restore its numerical
Hilbert--Schmidt norm before taking a polar, but cannot restore the missing
two source thirds: the polar support remains the character atom

```text
Y_a^*Y_a=z_(E,lambda_a),
lambda_a(j)=omega,       lambda_a(z)=omega^a,
lambda_a(w)=omega^2.
```

The D8 trace-factorization calculation now applies verbatim to `(QDS3)`
and gives

```text
||(polar(p_2Xp_a))V_eta||_2^2
 =tau(z_(E,lambda_a)f_eta)
 =(1/27)(1/32)
 =1/864.
```

The atoms for `a=0,1` are orthogonal, so at most `2/864` of the
selected pair survives. This proves the same-double-coset no-go and isolates
distinct double cosets as the next search space.
