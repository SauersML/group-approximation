---
rg: 2
id: nested-idempotent-padding-refutes-direct-finiteness
kind: route
title: Pad a nested-corner module isomorphism by the complement of the outer idempotent
target: leavitt-unit-group-algebra-not-directly-finite
requires:
  - leavitt-trace-balanced-nested-idempotents
  - leavitt-nested-idempotent-corner-module-equivalence
artifacts:
  - research/artifacts/kaplansky-cross-atlas-affine-lift-2026-09-07.md
---

## Proof

`leavitt-trace-balanced-nested-idempotents` supplies idempotents
`0 != f < e` in `S=F_2[Q]`, and
`leavitt-nested-idempotent-corner-module-equivalence` supplies `x in eSf`,
`y in fSe` with `xy=e` and `yx=f`.  Put

```text
X = x + (1-e),              Y = y + (1-e).
```

Because `f <= e` we have `f(1-e) = f - fe = 0` and `(1-e)f = 0`, so the cross
terms vanish:

```text
x(1-e) = (exf)(1-e) = ex . f(1-e) = 0,
(1-e)y = (1-e)(fye) = (1-e)f . ye = 0,
y(1-e) = (fye)(1-e) = fy . e(1-e) = 0,
(1-e)x = (1-e)(exf) = (1-e)e . xf = 0.
```

Therefore

```text
XY = xy + (1-e)^2 = e + (1-e) = 1,
YX = yx + (1-e)^2 = f + (1-e) = 1 - (e-f).
```

Since `f != e`, the idempotent `e-f` is nonzero and `YX != 1`.  So `S` is not
directly finite, which is the target.

Two remarks on what this route does and does not do.  It is a **sufficient**
condition only: a Kaplansky counterexample in `S` need not arise this way, so
a refutation of `(NIE1)` would close this route and leave the target open.
And the padding is the easy half — all the mathematics sits in the premise,
which is why that premise is carried as its own open claim rather than folded
into this route.
