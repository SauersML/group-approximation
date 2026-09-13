---
rg: 2
id: murray-z-only-any-inverse-from-symmetric-pieces
kind: route
title: Murray's shape has symmetric pieces, so a unit has inverse N^-1 u' and rescales into the ansatz over the algebraic closure
target: murray-z-only-shape-has-no-char0-units-any-inverse
requires:
  - promislow-symmetric-piece-units-satisfy-gardam-equations
  - murray-z-only-ansatz-has-no-char0-units
---

Notation as in the target.

**Step 1: the pieces are symmetric.** With `p0 = x^(-1/2) y^(-1/2) p`,
`q0 = y^(1/2) q`, `r0 = x^(-1/2) r` and `s0 = s`:

    p0 = (x^(1/2)+x^(-1/2)) (y^(1/2)+y^(-1/2)) f_1
    q0 = x^-1 y^(-1/2) (1+x)(x+y) f_2 + (y^(1/2)+y^(-1/2)) f_3
    r0 = x^(-1/2) y^-1 (1+y)(x+y) f_4 + (x^(1/2)+x^(-1/2)) f_5
    s0 = (x+4+x^-1+y+y^-1) f_6 + f_7

The substitution `x -> x^-1, y -> y^-1` fixes each `f_i(z)`, and it fixes each
displayed factor. For example, `x^-1 y^(-1/2) (1+x)(x+y)` becomes
`x y^(1/2) (1+x^-1)(x^-1+y^-1) = x^-1 y^(-1/2) (1+x)(x+y)`. The script checks
all four pieces exactly (log line `C3`).

**Step 2: the same `u'`.** The element `alpha'` of the requires, formed from
these pieces, is Murray's inverse candidate
`u' = x^-1 p_yz - x^-1 q a - y^-1 r b + z^-1 s_yz ab` of
`murray-z-only-ansatz-has-no-char0-units`, where `_yz` is `f -> f^A`. The
script checks this exactly (log line `C3`: "alpha' == Murray u': True").

**Step 3: rescaling.** Suppose `u` is a unit. By (3) of the first requires,
`u' u = N` with `N in K^x`.

- Choose `nu` in an algebraic closure `Kbar` with `nu^2 N = 1`.
- The element `nu u` has Murray's shape with `f_i` replaced by `nu f_i`, and
  `(nu u)' = nu u'` because `alpha -> alpha'` is linear. So
  `(nu u)' (nu u) = nu^2 N = 1` in `Kbar[P]`.
- By the second requires over the characteristic-0 field `Kbar`,
  `nu f_1 = ... = nu f_6 = 0` and `nu u = +-z^k ab`.

Hence `f_1 = ... = f_6 = 0` and `u = +-nu^-1 z^k ab`. Since `u in K[P]`,
`lambda = +-nu^-1` lies in `K^x`.

QED
