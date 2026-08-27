---
rg: 2
id: atlas-three-label-mode-weyl-wall-proof
kind: route
title: Evaluate fixed Weyl moments and invoke the authenticated commutator floor
target: atlas-three-label-mode-small-phase-weyl-hits-commutative-wall
requires:
  - atlas-three-label-mode-two-unitary-moment-reduction
  - leavitt-regular-atlas-block-monomial-gap
---

Repeatedly commute `S_r` past `D_r` using `(TWM0)`.  This proves `(TWM2)`.
The normalized trace of `S_r^a D_r^b` is zero unless both exponents vanish
modulo `r`.  Since each coefficient word in the fixed Atlas packet has
bounded length, for all sufficiently large `r` this is equivalent to
`a=b=0` as integers, proving `(TWM3)`.  The phase in the remaining case tends
to one, proving `(TWM4)` and the literal defect limit through `(TLM7)`.

For the quantitative obstruction, the Weyl relation directly gives
`(TWM5)`, and the same estimate holds for any choices of adjoints.  Each real
or imaginary part of a block coefficient is a fixed linear combination of

```text
I, S_r, S_r^*, D_r, D_r^*.
```

There are only finitely many label coefficients, uniformly bounded in `r`,
so the maximum commutator norm among all these real and imaginary block
parts tends to zero.  If the left side of `(TWM1)` had liminf zero, pass to a
subsequence on which the packet defect tends to zero.  That would be a
certificate sequence violating the fixed positive commutator floor `(BMG3)`.
Therefore the liminf is strictly positive.
