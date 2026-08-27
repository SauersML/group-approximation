---
rg: 2
id: bs14-r-fixed-source-block-proof
kind: route
title: Read inversion in blocks and evaluate the scalar orbit sum
target: bs14-trivial-boundary-inversion-forces-r-fixed-source
requires:
  - bs14-unitary-representations-are-periodic-cycle-packets
  - scalar-bs14-exit-angle-energy-dichotomy
---

Because `X~` is an involution, `X~R~X~=R~^(-1)` is equivalent to
`X~R~=R~^(-1)X~`.  Multiplying the two block matrices gives `(TBI2)`;
expanding `X~^2=1` gives `(TBI3)`.  The derivation of `(TBI4)` is the three
displayed boundary relations in the claim.

In the scalar packet basis, `R` is the cyclic shift with closing scalar `v`.
It has eigenvalue one exactly when `v=1`; the corresponding vector is the
orbit sum (after the harmless gauge which moves the closing phase to one
edge).  Applying the weighted shift formula `(SEG1)` to this vector averages
its weights and gives `(TBI5)`.

For `(TBI6)`, the order of four modulo `4^m-1` is exactly `m`: no smaller
positive `ell` can satisfy divisibility because `0<4^ell-1<4^m-1`.
Finally use `|1-exp(it)|<=|t|` and the geometric sum

```text
sum_(j=0)^(m-1) 4^j=(4^m-1)/3
```

to obtain `(TBI7)`.

