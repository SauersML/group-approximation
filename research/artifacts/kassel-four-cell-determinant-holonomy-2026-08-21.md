# The support-minimal mixed `C2` determinant holonomy cell

This is the exact local calculation in Kassel's root presentation that first
links the `beta` long-root central word to mixed, noncommuting `C2` relations.
It is deliberately only a determinant/abelian-shadow calculation; the final
section records why it does not prove the Maslov Hilbert--Schmidt gap.

Write the phases of

```text
x_alpha, x_beta, x_(alpha+beta), x_(2alpha+beta),
x_(-alpha), x_(-beta), x_(-(alpha+beta)), x_(-(2alpha+beta))
```

additively as `a,b,c,d,A,B,C,D` in `R/Z`.  The determinant shadows of
Kassel (2.4), (2.5), (2.6), and (2.12) are respectively

```text
r4  = c+d,
r5  = 2d,
r6  = -2B,
r12 = -c-b.
```

Indeed determinants erase the commutator on the left of each Chevalley
relation.  For

```text
w_beta = x_beta x_(-beta)^(-1) x_beta
```

the phase of `w_beta^4` is

```text
m = 8b-4B.
```

There is the exact integral identity

```text
m = -8 r4 + 4 r5 + 2 r6 - 8 r12.                 (K4)
```

Thus these four faces form a closed scalar holonomy certificate.  In
multiplicative notation `(K4)` gives, for scalar approximate relations,

```text
|w_beta^4-1|
 <= 8 delta_4 + 4 delta_5 + 2 delta_6 + 8 delta_12,
```

where `delta_i` is the chordal distance of the corresponding scalar relator
from one.

## Every face is essential

The support in `(K4)` is minimal.  If one relation is deleted, all the other
three can hold exactly while `m=1/3`, hence `w_beta^4=omega`:

```text
omit (2.4):   c=-1/24, b=1/24, d=B=0;
omit (2.5):   d=b=1/24, c=-1/24, B=0;
omit (2.6):   B=-1/12, b=c=d=0;
omit (2.12):  b=1/24, c=d=B=0.
```

All unlisted phases may be zero.  Direct substitution verifies the three
remaining equations in each row.  Therefore no proper subatlas of this
four-face determinant cell can carry the desired scalar holonomy payment.
In particular, (2.12) is the first relation that transports the free
`x_beta` phase into the short-root chain, while (2.4) closes that chain at
the other end.

## Why this does not give the matrix HS gap

For an exact `d`-dimensional matrix representation, `(K4)` proves only

```text
det(w_beta^4)=1.
```

This is compatible with `w_beta^4=omega I_d` whenever `3` divides `d`.
Moreover normalized determinant is not continuous in normalized
Hilbert--Schmidt distance uniformly in `d`: a scalar phase of order
`1/d` has vanishing normalized-HS distance from one but can have fixed
determinant.  Consequently `(K4)` cannot be promoted to a dimension-free
matrix estimate by taking determinants.

The positive-cycle lemma would promote a **single synchronized positive
Gram cycle** to such an estimate.  The calculation above identifies the
smallest possible cycle support and its coefficients, but the four
noncommuting Chevalley commutators do not themselves furnish compatible
positive Gram edges.  Constructing that common positive kernel is exactly
the still-open ucp-lifting/Maslov gap, not a consequence of the determinant
identity.

