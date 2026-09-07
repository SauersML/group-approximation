---
rg: 2
id: polar-corner-descent-retains-relator-error-proof
kind: route
title: Telescope compressed words and calibrate the quadratic loss in dimension two
target: polar-corner-descent-retains-relator-error
requires: []
---

It is enough to include both generators and their inverses among the unitary
letters; `(PCD1)` is unchanged under inversion. Write

```text
A_i=P U_i P |_ran(P).
```

The lower-right excursion gives

```text
I-A_i^*A_i=P U_i^*(I-P)U_iP,
||I-A_i^*A_i|| <= eta^2.                               (PCD4)
```

Thus `A_i` is invertible. If `V_i` is its polar unitary, its singular values
lie in `[sqrt(1-eta^2),1]`, and hence

```text
||V_i-A_i||
 <= 1-sqrt(1-eta^2)
 <= eta^2.                                             (PCD5)
```

For a word `r=x_(i_1)...x_(i_ell)`, replacing its polar factors one at a
time gives

```text
||r(V)-A_(i_1)...A_(i_ell)|| <= ell eta^2.              (PCD6)
```

Now insert the internal copies of `P` into `P r(U)P` from right to left. At
the cut after the first `j` letters, the error term is bounded by

```text
||P U_(i_1)...U_(i_j)(I-P)||
  ||(I-P)U_(i_(j+1))P||
 <= j eta^2.                                           (PCD7)
```

The first factor is bounded by `j eta` by telescoping the commutator of `P`
with a product; the second is at most `eta`. Summing `(PCD7)` for
`j=1,...,ell-1` gives

```text
||A_(i_1)...A_(i_ell)-P r(U)P||
 <= ell(ell-1) eta^2/2.                                (PCD8)
```

Combining `(PCD6)` and `(PCD8)`, then using

```text
||P r(U)P-P|| <= ||r(U)-I||,
```

proves `(PCD2)` and `(PCD3)`.

For the calibration, let `c=cos(theta)`, `s=sin(theta)` and put

```text
U=[[c,is],[is,c]],
V=[[c,s],[-s,c]],
W=UV,
P=diag(1,0).                                            (PCD9)
```

The relation `UV=W` is exact. The compressed polar parts of `U` and `V` are
both `1`, while

```text
PWP=(c^2-is^2)P
```

has polar part

```text
lambda_theta=(c^2-is^2)/|c^2-is^2|.
```

Thus the descended relation has defect

```text
|1-lambda_theta|=theta^2+O(theta^4),                   (PCD10)
```

whereas the commutator leakage is `O(theta)`. This proves that the quadratic
term is a real phenomenon even for an exact relation. The example was also
checked numerically at `theta=0.1,0.03,0.01`, with the quotient of the defect
by `theta^2` tending to one.
