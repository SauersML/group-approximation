---
rg: 2
id: radial-partitioned-involution-code-coloring-proof
kind: route
title: Split involution carriers into disjoint affine codewords
target: radial-simplex-excludes-partitioned-involution-targets
requires:
  - radial-only-group-needs-a-cyclic-gcd-audit
---

Fix a partitioned-involution target `T` and a homomorphism from the canonical
radial group.  In one radial context, all nonidentity coordinate images
commute, hence lie in one elementary abelian carrier `E_t`.  Keeping only
one carrier therefore preserves every local product equation.  Composing
with each linear functional on `E_t` and using `(RGA4)` shows that this
carrier component is an `E_t`-valued affine function on `K`.

Here is the only extremal fact required.  If nonzero affine maps `F,G` on
an `n`-dimensional binary space have disjoint supports away from zero, their
zero sets are proper affine subspaces whose union contains at least
`2^n-1` points.  Each has size at most `2^(n-1)`.  For `n>=3`, replacing
either hyperplane by a subspace of codimension at least two makes the union
too small.  Hence both are hyperplanes.  Two nonparallel affine hyperplanes
intersect in `2^(n-2)>=2` points, so their intersection could not be confined
to `{0}`.  They are therefore parallel and distinct: their zero sets are
complementary, and each map has rank one.  This also shows that no third
nonempty disjoint support exists.

With two carriers, all nonzero coordinates are occupied and the two support
indicators are complementary affine half-spaces.  Every radial four-set must
be monochromatic because elements from distinct carriers cannot commute.
The contained edge `{x,alpha x}` then makes the indicator invariant under
multiplication by `alpha`, hence constant on `K^*`.  Its affine-half-space
weight is neither zero nor `2^n-1`, a contradiction.  One carrier remains,
so the image is elementary abelian.

In `PSL_2(2^r)`, the root subgroups indexed by projective-line points are
elementary abelian, partition the nontrivial involutions, and are the full
involution centralizers.  This supplies the target family and includes
`PSL_2(4)=A5`.
