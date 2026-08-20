---
rg: 2
id: atlas-root-energy-ellipse-controls-s3-distance-proof
kind: route
title: Optimize the weighted Cayley inequalities against the exact t21 triangle envelope
target: atlas-root-energy-ellipse-controls-s3-distance
requires:
  - s3-weighted-two-generator-covariance-controls-commutant-distance
  - s3-weighted-budget-optimization
  - atlas-19243-relation-forces-s3-distance
---

Put

```text
A=S^2,
B=x_12^2,
d=dist_2(U,C_K).
```

The audited positive word for `t21` gives directly

```text
a <= sqrt(2)S,
```

and the other raw involution is `t12`, so

```text
b^2=2B.
```

For every `p,q>0`, the weighted S3 covariance theorem therefore gives

```text
lambda(p,q)d^2
 <= p a^2+q b^2
 <=2(pA+qB).
```

If `d=0` there is nothing to prove.  Otherwise divide by `pA+qB` and take the
supremum over weights.  The closed-form optimization theorem yields

```text
3/[2(A+B+sqrt(AB))] <= 2/d^2.
```

Hence

```text
A+B+sqrt(AB) >= 3d^2/4.
```

Because `sqrt(AB)=S x_12`, the left side is exactly the root-energy ellipse
functional `F`.

Finally substitute the established packet estimate

```text
d >= max(0,(sqrt(2)-L_19243 delta)/16)
```

to obtain `(ROOT-19243-WALL)`.  Sending `delta->0` gives

```text
(3/4)(sqrt(2)/16)^2=3/512.
```

Thus the open A4 ceiling is attempting to cross an exact dual wall, not a chain
of loose symmetric relaxations.

For the quotient-necessity sequence, use the collision relation itself instead:

```text
d >= max(0,(sqrt(2)-||q_19243(U)-1||_2)/8).
```

Substitution into `F>=3d^2/4` proves `(ROOT-19243-REL-WALL)`.  Since the
pulled-back kernel relation has defect tending to zero, its limiting wall is

```text
(3/4)(sqrt(2)/8)^2=3/128.
```

No Cayley-gap or triangle constant changes; the factor-four improvement comes
solely from avoiding the extra `q^*` occurrence in the centrality commutator.
