---
rg: 2
id: authenticated-mixed-loop-kills-cubic-affine-modules
kind: claim
title: The authenticated mixed loop kills cubic defining-module gauges
artifacts:
  - research/authenticated-mixed-loop-cubic-module-proof.md
distinct_from:
  authenticated-mixed-loop-kills-quadratic-affine-modules: that closes the two pure quadratic fundamental blocks; this proves the next defining-module symmetric power with a characteristic-uniform minor certificate.
  rank-one-closure-excludes-noncentral-outlier-gauges: that asks for arbitrary unitary or nonlinear gauges and noncongruence actors; this remains an exact defining-characteristic polynomial-module theorem.
---

Use the honest coefficient actor and odd-characteristic field from the
previous authenticated affine claims.  The two Fox rows have zero common
kernel on

```text
Sym^3(K^3)                                               (CAM1)
```

and on every Frobenius twist of `(CAM1)`.  The conclusion is uniform over
all odd characteristics, including `3` and `5`: two complementary minors of
the authenticated row have determinants `24` and `-20`, whose only common
prime divisor is `2`.

The same conclusion also holds on

```text
Sym^3((K^3)^*).                                        (CAM2)
```

Away from characteristic three the torus kernel is a single explicit line
and the authenticated row is nonzero on it.  In characteristic three the
torus rank drops, but a separate full minor of the stacked two-row operator
has determinant `-91/64`, so the extra directions are also killed.

Consequently every module filtered by the previously established blocks and
arbitrary copies or twists of `(CAM1)` and `(CAM2)` also has zero affine
gauge.  This pushes the first unresolved symmetric powers on both fundamental
sides to degree four.  It does not prove the universal group-algebra ideal
statement.

DERIVATION
authenticated-mixed-loop-cubic-module-proof
