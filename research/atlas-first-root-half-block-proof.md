---
rg: 2
id: atlas-first-root-half-block-proof
kind: route
title: Read root_12_1e as a commutator and pinch it by the fixed transvection
target: atlas-first-root-relator-is-half-block-commutant-face
requires:
  - atlas-three-label-mode-two-unitary-moment-reduction
---

The deterministic rank-five dictionary gives

```text
x_12(1) = (1, I+E_34),

x_12(e) = (1,I+E_31)(2,I+E_32)(1,I+E_31)(2,I+E_32)
          (1,I+E_24)(2,I+E_32)(1,I+E_31)(2,I+E_32)
          (1,I+E_24+E_31).                           (FRP1)
```

The last first-chart matrix is `(I+E_24)(I+E_31)`, so after representing the
second chart by conjugation with `U_Z`, `(FRP1)` is exactly `(FRF1)`--`(FRF2)`.
The first full-family relation is root-subgroup commutativity

```text
root_12_1e = [x_12(1),x_12(e)],                       (FRP2)
```

which proves `(FRF3)`.  Expanding its eight transported slots by `(TLM5)`
gives the left side of `(FRF6)` without making any Weyl or commutativity
assumption on `Z_1,Z_2`.

It remains to expose the positivity hidden in that affine expansion.  Since
`G=2R-I` and `B_Z` is unitary,

```text
||G B_Z G B_Z^* - I||_2
 = ||G B_Z-B_Z G||_2.                                (FRP3)
```

Relative to `R direct-sum (I-R)`, the additive commutator `G B_Z-B_Z G`
has only the two off-diagonal blocks, each multiplied by `2`.  Orthogonality
of the two corners therefore gives

```text
||G B_Z-B_Z G||_2^2
 =4(||R B_Z(I-R)||_2^2+||(I-R)B_ZR||_2^2).           (FRP4)
```

For any unitary `V`, `||V-I||_2^2=2-2 Re tr(V)`.  Combining this with
`(FRP3)`--`(FRP4)` proves `(FRF5)`--`(FRF7)`.  It also gives the quantitative
pinching identity

```text
||B_Z-[R B_Z R+(I-R)B_Z(I-R)]||_2
  = (1/2)||[G,B_Z]-I||_2.                            (FRP5)
```

Finally `atlas-first-rank-five-relator-kills-order-one-weyl-slice` computes
the Weyl value of the left side of `(FRF6)` as
`16953689/41287680`.  Substitution into `(FRF6)` yields `(FRF8)` exactly.
