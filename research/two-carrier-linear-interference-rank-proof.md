---
rg: 2
id: two-carrier-linear-interference-rank-proof
kind: route
title: Row-reduce the join of two hidden-sign carrier supports
target: two-carrier-linear-interference-misses-target-by-five-over-2304
requires:
  - two-c-conjugate-g2-mixed-carriers-collapse-to-one-orientation
---

## 1. A coefficient-independent support bound

From `(TCC3)` and the single-carrier polar calculation,

```text
X_i^*X_i=K_i=G_(sigma,+)(1+Z_i)/2.
```

Therefore `X_i=X_iK_i`. Since `K_0,K_1` commute, their join is

```text
L_sigma=K_0+K_1-K_0K_1
 =G_(sigma,+)(1-(1-Z_0)(1-Z_1)/4).                     (LIF6)
```

For arbitrary complex `lambda_i`,

```text
X_lambda=X_lambda L_sigma.
```

If `L_sigma Rv=0`, then `X_lambda Rv=0`. It follows that

```text
supp abs(X_lambda R) <= supp abs(L_sigma R).             (LIF7)
```

This argument includes every cross term and does not require the two
summands to have orthogonal ranges. A left contraction, in particular
`Ee_b g_2^j`, preserves the same upper bound.

## 2. Fourier description of the join

Work in the active finite group `F_act` of order `6144` from
`(GMR15)--(GMR16)`. Put

```text
B_2=<H,A,W,Z_0,Z_1> isomorphic to C_2^5.
```

Fix the signs `H=-1,A=sigma,W=+1`. The join in `(LIF6)` is the sum of
the three `B_2` Fourier characters with hidden-sign values

```text
(Z_0,Z_1)=(+,+),(+,-),(-,+).
```

Only the `(-,-)` atom is omitted. Thus the right ideal cut by
`L_sigma` has a basis indexed by

```text
3*(|F_act|/|B_2|)=3*(6144/32)=576
```

character-coset rows. The fixed quotient character of
`<k> isomorphic to C_3` gives `6144/3=2048` columns.

For a column represented by `<k>g` and one of the three hidden
characters, the only possible entries occur at

```text
B_2g,                  B_2kg,                  B_2k^2g
```

with cyclotomic coefficients `1,omega^2,omega` and the appropriate
`B_2` character factor. Stacking the three character blocks gives at
most nine entries per uncollected column.

## 3. Exact cyclotomic elimination

Encode each coefficient-ring entry by its triple in
`D=span_(F_2){1,q,a}` and enumerate the same `6144` canonical
six-by-six matrices as in the one-hidden-sign certificate. Assign their
`B_2` and `<k>` cosets, form the `576 by 2048` incidence matrix just
described, and row-reduce over

```text
Q[omega]/(omega^2+omega+1).
```

The exact pivot table is

| `sigma` | rows | columns | pivots |
|---|---:|---:|---:|
| `+` | 576 | 2048 | 492 |
| `-` | 576 | 2048 | 468 |

During elimination the largest pivot-row support is `39` and every
numerator and denominator has at most four binary digits. Hence this is
an exact characteristic-zero certificate, not a modular-rank lower bound
or a floating-point estimate.

As before, `R` selects two central `h` characters. The full finite group
has order `3*6144=18432`, so

```text
2*492/18432=41/768,
2*468/18432=13/256.                                    (LIF8)
```

Converting to denominator `2304`,

```text
41/768=123/2304,              13/256=117/2304,
1/18=128/2304.                                         (LIF9)
```

Equations `(LIF7)--(LIF9)` prove the claim. In particular even the full
join of the two possible initial supports, which is a stronger allowance
than any fixed linear combination, remains five units of
`1/2304` below the all-plus target capacity.
