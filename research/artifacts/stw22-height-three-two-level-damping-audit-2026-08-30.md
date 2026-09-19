# STW XXII: height-three scattered two-level damping audit

## The extra level

Near a Cantor--Bendixson rank-two point, a compact metrizable scattered
space decomposes into clopen rank-one blocks converging to the point.  The
fibre gap is therefore a reduced product of the uniform completions of
those blocks, not a raw product of factors.  Coordinatewise unitaries need
not be continuous at the inner limit points.

## Resolution

Evaluate at one distinguished point in every block.  The quotient is the
rank-one cofinite corona and is already bounded-trace-free.  In the kernel,
positive representatives can be cut down by a norm-null scalar sequence so
that they vanish exactly at all distinguished points.

For a spectral cut `c`, choose the desired orthogonalizers independently in
each isolated fibre, but retain only the products

```text
u_j c^(1/2).
```

Their `2`-norms tend to zero at every inner limit point because `c` does,
so the products are continuous even though the unitaries are not.  Their
range elements are orthogonal and their source elements all equal `c`,
which kills every bounded trace by arbitrary finite replication.

## Scope

This proves automatic trace continuity for the trivial UHF field over every
compact metrizable scattered space with third derivative empty.  It is not
a claim about nontrivial bundles.  Iterating the damping construction to
higher Cantor--Bendixson rank would require organizing successive skeleton
quotients and is not included here.
