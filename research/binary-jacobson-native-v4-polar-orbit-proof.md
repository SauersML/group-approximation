---
rg: 2
id: binary-jacobson-native-v4-polar-orbit-proof
kind: route
title: Track the z and Y signs under the two commuting native source-row roots
target: binary-jacobson-native-v4-polar-orbit-leaves-one-residual
requires:
  - binary-jacobson-first-alternating-polar-is-half-supported
  - binary-jacobson-constant-opposite-polar-is-finite-s3
---

All defining cuts of `e=F_+` are spectral cuts of roots in position `(1,3)`.
The roots `X=x_12(Q)` and `b=x_12(1)` commute with that whole root subgroup,
so they preserve `e`; they also commute with one another and with
`alpha=x_13(1)`.

The four Heisenberg commutators are

```text
X z X=x_13(Q)z=-z,
X Y X=x_13(Q)Y=-Y,
b z b=alpha z,
b Y b=x_13(Q)Y=-Y,                                     (1)
```

where the head root acts as `-1` on `e`.  This proves `(JV43)`.

If `alpha=+1`, the two sign transformations in `(JV43)` are independent:
`X` flips both signs and `b` flips only `Y`.  Starting at `(+,+)` gives all
four pairs in `(JV44)` exactly once.  Their spectral projections are
orthogonal and sum to the full `alpha=+1` part of `e`.

If `alpha=-1`, both `X` and `b` flip both signs.  Their orbit of `(+,+)` is
only `{(+,+),(-,-)}`.  Those are exactly the `zY=+1` sectors, so their
complement inside the negative `alpha` cut is `(JV46)`.

Finally the constant matrices in the `(1,3)` block give

```text
x_31(1)x_13(Q)x_31(1)
 =I+Q E_13+Q E_31+Q(E_11+E_33),                         (2)
```

which is not a same-position root and does not commute with `x_13(Q)` in
the faithful Jacobson action.  Hence `x_31(1)` does not normalize even the
head cut defining `e`, much less all three raw cuts.  Its conjugate of `p`
therefore cannot be added to the internal orbit as a subprojection of `e`
without a new compression calculation.  Its constant negative-cut polar is
computed in the finite `S_3` prerequisite, but compression by `e_res` is new
mixed data.  This proves the stated boundary.
