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
contractions.  Closeness to the target unitaries gives all four Schwarz
defect bounds

```text
||1-x^*x||, ||1-xx^*|| <=2 epsilon_U,
||1-y^*y||, ||1-yy^*|| <=2 epsilon_d.                (UCP1)
```

For example,

```text
||1-x^*x||
 <=||U^*(U-x)||+||(U^*-x^*)x||
 <=2 epsilon_U,                                      (UCP2)
```

and the other estimates are identical.

Choose a Stinespring representation `Phi(c)=V^*pi(c)V` and put
`P=VV^*`.  Cauchy--Schwarz in the two off-range factors gives

```text
||Phi(ab)-xy||
 =||V^*pi(a)(1-P)pi(b)V||
 <=||V^*pi(a)(1-P)|| ||(1-P)pi(b)V||
 <=2 sqrt(epsilon_U epsilon_d).                       (UCP3)
```

Indeed, the squares of the last two norms are bounded respectively by
`||1-xx^*||` and `||1-y^*y||`.  Applying the same computation to `ba`
gives

```text
||Phi(ba)-yx||<=2 sqrt(epsilon_U epsilon_d).           (UCP4)
```

Since `ab=ba`, equations `(UCP3)--(UCP4)` imply

```text
||[x,y]||<=4 sqrt(epsilon_U epsilon_d).                (UCP5)
```

Finally,

```text
||[U,d]-[x,y]||
 <=||Ud-xy||+||dU-yx||
 <=2(epsilon_U+epsilon_d).                            (UCP6)
```

Combining `(UCP5)` and `(UCP6)` proves `(UCG2)`, and setting the two
errors equal proves `(UCG3)`.

If `y=d` is unitary, equality holds in both Schwarz inequalities for `b`.
Thus `b` belongs to the multiplicative domain of `Phi`.  Since `a` and `b`
commute,

```text
x d=Phi(a)Phi(b)=Phi(ab)=Phi(ba)=Phi(b)Phi(a)=d x.
```

Perturbing `x` to `U` now costs at most `2 epsilon_U` in the commutator,
which proves `(UCG4)`.  The argument is symmetric if the circle generator
is returned exactly.
