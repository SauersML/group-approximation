# STW XL trace-boundary extraction audit (2026-08-30)

## Result

Every amenable action of a nonamenable countable group on a unital separable
nuclear algebra with traces contains a nontrivial minimal strongly proximal
compact subsystem inside its trace simplex.

## Load-bearing checks

1. A minimal nonempty compact convex invariant trace set exists because a
   nested family has nonempty compact intersection.
2. The closure of its extreme points is invariant under affine
   homeomorphisms.
3. If a compact subset has dense convex hull, it contains all extreme points:
   finite convex combinations become probability measures, and an extreme
   point has only its point mass as a representing measure.
4. This observation makes the extreme-point closure minimal: any closed
   invariant subset has invariant closed convex hull, which must be the whole
   minimal affine set.
5. For a probability measure on the extreme-point closure, convex density of
   the orbit of its barycenter produces the point mass at an extreme point in
   the closed convex hull of the measure orbit.
6. Applying the same extreme-point observation in the probability-measure
   simplex removes the convex combinations and puts that point mass in the
   actual orbit closure.  This is exactly strong proximality.
7. A singleton boundary would be an invariant trace, already excluded for an
   amenable action of a nonamenable group.

## Consequence for the construction problem

The earlier obstruction ruled out invariant measures and equicontinuous
trace islands.  This theorem supplies the positive structural replacement:
every witness necessarily realizes a genuine group boundary in `T(A)`.
What remains open is the C-star realization problem—constructing an amenable
action on a stably finite classifiable algebra whose induced trace action
contains such a boundary while retaining simplicity and classification.
