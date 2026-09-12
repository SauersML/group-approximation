# Audit: bounded-overlap duplicated Fourier colours

Date: 2026-08-30

## Norm-concentration estimate

Approximation at the unit forces the sum of the colour units to have norm
at least `1-epsilon`.  One of `r` colours therefore has norm at least
`(1-epsilon)/r`.  Bounded overlap concentrates at least a `1/M` fraction
of that norm in one coordinate.  Positivity prevents the other colours
from cancelling this coordinate, whereas its weighted-average target has
norm exactly `1/n`.  Rearrangement gives the stated elementary bound
`(1-rM/n)/(rM+1)`.

## Covered constructions

Order-zero images of the coordinate atoms are orthogonal and have overlap
constant one.  Scalar duplication, Fejer weights, and tent weights do not
change that.  If a band support graph has chromatic number at most `M`, its
images split into `M` orthogonal packets and satisfy the required norm
inequality.  The argument therefore permits arbitrary duplication and
overlapping windows while ruling out every uniformly bounded overlap
profile.

## Boundary

The composed maps from the Fourier diagonal need not be order zero in a
general nuclear-dimension factorization: a c.p. incoming map may mix the
minimal diagonal projections before the order-zero return.  Such mixing
can make the norm of a colour unit much larger than every individual
coordinate image, forcing `M` to grow with `n`.  The theorem proves this
growth is necessary; it does not exclude it and does not decide finite
nuclear dimension of the cyclic augmentation ideal.
