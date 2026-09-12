---
rg: 2
id: titz-witzel-involution-sandwich-proof
kind: route
title: Replace the two surviving quartics by a square-root chain and an involution sandwich
target: titz-witzel-two-generator-involution-sandwich-normal-form
requires:
  - titz-witzel-sofic-gate-two-generators-four-approximate-relators
---

Write `P_0,Q` for the fourth and fifth relators in `(TW2G2)`.  Since
`x=a u^2`, free cancellation gives

```text
P_0 = b a u d^(-1),                 Q = a c d b.             (1)
```

The third relator in `(TW2G2)`, using `e^2=1`, is

```text
R_0=rho^2 e u^(-1)=1.                                      (2)
```

It implies `u=rho^2e`, and therefore

```text
b=rho u^(-1)rho
  =rho e rho^(-2)rho
  =rho e rho^(-1)
  =beta.                                                    (3)
```

Thus, modulo `R_0`, the relator `P_0` is exactly

```text
P=beta a u d^(-1).                                         (4)
```

Next impose `P_0=1`.  Equation (1) then gives

```text
b=d u^(-1)a.                                               (5)
```

Substitution in `Q` gives

```text
Q=a c d^2u^(-1)a.                                         (6)
```

Conjugating (6) by `a` and cyclically conjugating the resulting word shows
that `Q=1` is equivalent to

```text
W=d^2u^(-1)c=1.                                            (7)
```

No involution relation for `c` is needed for this cyclic-conjugacy step.
Conversely, (5) and (7), now using the retained relation `c^2=1`, give

```text
Q=a c d^2u^(-1)a=a c c a=1.                               (8)
```

This proves the exact square-root-chain presentation.

Under (3)--(4), put `p=beta a`.  Then `d=pu`, and substitution in (7)
freely gives

```text
W=(pu)^2u^(-1)c=pupc.                                     (9)
```

This proves `(TWIS2)`.  The substitutions are reversible and use only
relators retained in the new presentation, so this is an exact finite
Tietze transformation rather than a quotient comparison.  Since `e` is an
involution, the definitions

```text
h=ueu^(-1),   a=ehe,   f=x^(-1)hx,   s=faf,
beta=rho e rho^(-1)
```

also prove directly that all five displayed words are involutions.  The
generator `u` was never changed, so the mark is still `u^8`.

For the metric statement, first observe from (2)--(3), before imposing the
relator, that bi-invariance gives the exact equality

```text
d(b,beta)=d(R_0,1)=delta_0.                               (10)
```

Replacing the single occurrence of `b` in `P_0` by `beta` proves the first
inequality in `(TWIS6)`.  The defect `delta_P` is also exactly
`d(b,d u^(-1)a)`.  Replacing `b` by `d u^(-1)a` in `Q` changes its defect by
at most `delta_P`; the resulting word is (6), whose defect is exactly that
of `W` by conjugacy and cyclic conjugacy.  This proves both middle
inequalities.

Finally replace the two occurrences of `d` in `W` by `pu`.  Each replacement
costs at most `eta_P`, and the resulting word freely reduces to `pupc`.
This proves the last inequality.  The same estimates in the reverse
direction prove the asserted equivalence of vanishing defects.

The attached dependency-free checker verifies the free-word identities and
also exhaustively tests `(TWIS6)` on small random permutation instances.  It
is a transcription check; the Tietze argument is the calculation above.
