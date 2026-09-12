---
rg: 2
id: atlas-collision-order-zero-wall-on-s3-flat
kind: claim
title: Collision has an order-zero wall on the packet S3 tangent flat
distinct_from:
  atlas-fourteen-shifted-tangent-spaces-have-an-s3-flat: that constructs the exact common packet tangent flat; this determines what collision does along exponentials of those directions at the reference packet point.
  atlas-a4-classical-opaque-star-sharp-constant: that computes collision on all sixty discrete classical alignments; this supplies a quantitative neighbourhood exclusion for arbitrary matrix tangent directions.
---

Let `R` be the frozen inner reference alignment in `Reg(A8) tensor I_k`, and
let `T` be any skew-Hermitian tangent vector, in particular any vector in the
exact `S3` flat of
`atlas-fourteen-shifted-tangent-spaces-have-an-s3-flat`.  Put

```text
U(epsilon)=exp(epsilon T)R.
```

Then collision is already nonzero at order zero:

```text
||q_19243(R)-1||_2=sqrt(2).                            (A4-Q0-1)
```

Moreover the four occurrences of the conjugated collision involution give
the dimension-free bound

```text
||q_19243(U(epsilon))-1||_2
 >= sqrt(2)-8 |epsilon| ||T||_2.                       (A4-Q0-2)
```

Thus for a normalized tangent direction, collision has no zero on

```text
|epsilon|<sqrt(2)/8.                                   (A4-Q0-3)
```

In particular there is no exact or analytic collision-zero curve through
`R`, whether tangent to the 3360-dimensional `S3` packet flat or not.  The
first nonzero term in the collision-defect expansion is the constant term,
not a Hessian or quartic form.  Consequently coercivity of the collision
Hessian at `R` is not the missing joint estimate: `R` does not lie on the
joint packet--collision zero fiber.

This sharply limits the tangent method.  A sequence with all fourteen packet
distances and collision defect tending to zero cannot remain in a vanishing
Hilbert--Schmidt neighbourhood of any one classical packet alignment.  Any
successful argument must either control the global nonlinear geometry of the
simultaneous shifted-double-coset intersection, or first produce/locate a
genuine joint zero (or ultralimit zero) and linearize there.
