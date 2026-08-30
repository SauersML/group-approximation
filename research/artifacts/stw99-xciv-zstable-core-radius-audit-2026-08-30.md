# STW Problem XCIV: Jiang--Su-stable norm-core radius audit

## A second mechanism beyond commutant capacity

The commutant-capacious radius controls a tuple by placing an exact
`I_(2,3)` in the relative commutant of a nearby core.  This is not the only
source of local block copies.  If a nearby norm core is itself `Z`-stable, it
produces approximately central copies internally, whether or not its ambient
commutant is large.

For a finite tuple `F`, let `zeta_Z(F)` be its best operator-norm distance to
a separable unital `Z`-stable subalgebra of `R`.  Internal absorption and the
triangle inequality give

```text
gamma_(I_(2,3))(F)<=2 zeta_Z(F).
```

This includes simple nuclear infinite-dimensional finite-nuclear-dimension
cores by the finite-nuclear-dimension theorem for `Z`-stability.

## Scalar-commutant test

The tracial GNS representation of `Z` is faithful and has weak closure `R`.
Its image is therefore a separable unital `Z`-stable C*-subalgebra with
scalar relative commutant in `R`.  Every finite tuple in that image has zero
fixed-block defect, with the approximately central block maps lying inside
the weakly dense image itself.

Thus a proof based only on finding an exact noncommutative algebra in the
ambient commutant misses a genuine positive mechanism.  Operator-norm
centrality need not converge to exact centrality inside `R`.

## Obstruction sharpened

A negative fixed-block gap `delta` forces distance at least `delta/2` from
every separable `Z`-stable norm core.  Combined with the earlier radii, a
counterexample tuple must simultaneously avoid finite-dimensional
subalgebras, tensor-split/commutant-capacious cores, and all internally
`Z`-stable cores.

Showing that one of these regular cores approaches every finite tuple would
settle XCIV.  Hyperfinite `2`-norm approximation supplies none of these
operator-norm distances.
