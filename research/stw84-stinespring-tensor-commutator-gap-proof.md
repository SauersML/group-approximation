---
rg: 2
id: stw84-stinespring-tensor-commutator-gap-proof
kind: route
title: Convert near-unitaries into Stinespring multiplicative defects
target: stw84-untwisted-coefficient-symbols-pay-covariance-gap
requires:
  - stw84-scalar-fourier-row-two-colour
  - stw84-invariant-coefficient-stages-restore-two-fourier-colours
artifacts:
  - research/artifacts/stw84-untwisted-coefficient-covariance-gap-audit-2026-08-30.md
---

Put

```text
a=z tensor 1,       b=1 tensor v,
x=Phi(a),           y=Phi(b).
```

Thus `a` and `b` are commuting unitaries, while `x` and `y` are
contractions.  Write `e=Phi(1)`.  Closeness to the target unitaries and
`||e-1||=eta` give all four Schwarz defect bounds

```text
||e-x^*x||, ||e-xx^*|| <=eta+2 epsilon_U,
||e-y^*y||, ||e-yy^*|| <=eta+2 epsilon_d.             (UCP1)
```

For example,

```text
||e-x^*x||
 <=||e-1||+||U^*(U-x)||+||(U^*-x^*)x||
 <=eta+2 epsilon_U,                                  (UCP2)
```

and the other estimates are identical.

Choose a Stinespring representation `Phi(c)=V^*pi(c)V`; here `V` is a
contraction and `P=VV^*<=1`.  Cauchy--Schwarz through `(1-P)^(1/2)` gives

```text
||Phi(ab)-xy||
 =||V^*pi(a)(1-P)pi(b)V||
 <=||V^*pi(a)(1-P)|| ||(1-P)pi(b)V||
 <=sqrt((eta+2epsilon_U)(eta+2epsilon_d)).             (UCP3)
```

Indeed, the squares of the last two norms are bounded respectively by
`||e-xx^*||` and `||e-y^*y||`.  Applying the same computation to `ba`
gives

```text
||Phi(ba)-yx||
 <=sqrt((eta+2epsilon_U)(eta+2epsilon_d)).             (UCP4)
```

Since `ab=ba`, equations `(UCP3)--(UCP4)` imply

```text
||[x,y]||
 <=2 sqrt((eta+2epsilon_U)(eta+2epsilon_d)).           (UCP5)
```

Finally,

```text
||[U,d]-[x,y]||
 <=||Ud-xy||+||dU-yx||
 <=2(epsilon_U+epsilon_d).                            (UCP6)
```

Combining `(UCP5)` and `(UCP6)` proves `(UCG2)`, and setting the two
errors equal proves `(UCG3)`.

If `y=d` is unitary, Schwarz gives `1=d^*d<=Phi(1)<=1`, so `Phi` is unital,
and equality holds in both Schwarz inequalities for `b`.  Thus `b` belongs
to the multiplicative domain of `Phi`.  Since `a` and `b`
commute,

```text
x d=Phi(a)Phi(b)=Phi(ab)=Phi(ba)=Phi(b)Phi(a)=d x.
```

Perturbing `x` to `U` now costs at most `2 epsilon_U` in the commutator,
which proves `(UCG4)`.  The argument is symmetric if the circle generator
is returned exactly.
