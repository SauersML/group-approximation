# The ordinary singleton line has a uniform matching decoder

Date: 2026-08-11

## Outcome

For every odd prime `p`, the ordinary singleton fibre in the first positive
vertex-resolution row is the Veronese projective line

`L_p={v(t):t in F_p} union {v(infinity)}`,                       `(PSM1)`

where

`v(t)=[1:2:t:4:2t:t^2]`,
`v(infinity)=[0:0:0:0:0:1]`.                                   `(PSM2)`

One fixed total-degree-three Wall generator has boundary

`d c_t=e_(v(t))+e_(v(2-t))`.                                    `(PSM3)`

This is an identity over `Q(t)`, so it specializes to every odd prime.  The
involution `t -> 2-t` has exactly two projective fixed points:

`t=1` and `t=infinity`.                                         `(PSM4)`

The fixed-point difference is the boundary of the exact four-term rational
chain already isolated in `TRUE_PROJECTIVE_DERIVED_E1_AUDIT.md`.  Combining
the one-row fills for nonfixed pairs with this four-term fill gives a right
inverse of norm exactly

`sqrt(2)`                                                       `(PSM5)`

on the matching-difference subspace of the ordinary singleton line,
independently of `p`.

This is a uniform quantitative theorem.  It does not yet decode the quotient
which retains one coordinate for each involution pair.  The remaining
positive-primary problem is therefore the Wall differential on that smaller
pair-orbit module, not the original `p+1` singleton coordinates.

There is no conflict with
`TRUE_BOUNDED_DEGREE_PARITY_DECODER_NO_GO.md`.  The section here acts only on
the orthogonal direct sum of differences inside disjoint matched pairs.  A
demand between two different pair-orbit coordinates is absent from its
domain and can still require a path of growing length in any bounded-degree
graph-only decoder.  The theorem removes one uniformly split summand; it
does not claim an integral section of the full augmentation lattice.

## Exact rational identity

Let `R` be HAP's free Wall resolution

`ResolutionArithmeticGroup("SL(3,Z)",3)`.

The fourth `q=0`, total-degree-three generator has twenty group-ring boundary
terms before specialization.  Evaluate those terms on the rational function
point `v(t)` and reduce coefficients modulo two.  Eighteen terms cancel in
pairs and the residual is exactly

`[0,v(t)]+[0,v(2-t)]`,                                          `(PSM6)`

where `0` denotes the first total-degree-two resolution generator.  Direct
evaluation at `v(1)` and `v(infinity)` gives zero, as required by `(PSM4)`.

The calculation is symbolic over `Q(t)`, not interpolation from finite
fields.  It is checked by
`experiments/sl3_projective_q0_relation_exact.g`.  The committed stdout
certificate is `experiments/sl3-projective-q0-relation-exact.txt`, with
SHA-256
`6d6e924f94c7af378a0a49fc923eafbf97a3eed8b1afab605664532598249219`.

## Uniform splitting norm

Partition `L_p` into the orbits of `t -> 2-t`.  There are `(p-1)/2`
nonfixed pairs and the two singleton fixed points.  Choose one source basis
vector `c_t` for each nonfixed pair.  These chosen vectors are distinct
coordinate vectors, hence orthonormal, and their boundaries are the
pair-difference vectors from `(PSM3)`.  Those boundaries have disjoint
supports and squared norm two.

Let `C_*` be the four-term chain with

`d C_*=e_(v(1))+e_(v(infinity))`.                               `(PSM7)`

Its four source coordinates are disjoint from the fourth-generator
coordinates used by the one-row matching fills.  Thus the source Gram matrix
for the combined section is

`diag(1,...,1,4)`,                                              `(PSM8)`

while the target pair-difference Gram matrix is `2I`.  The largest generalized
eigenvalue is `4/2=2`, proving `(PSM5)`.

Equivalently, if `D_p` is the span of the difference vector in every
two-element orbit together with the difference of the two fixed points,
then

`d:J_p(D_p)->D_p`, `d J_p=id`, `||J_p||=sqrt(2)`.               `(PSM9)`

All assertions are over `F_2` with coordinate Euclidean norms.  This is the
bounded-primary cancellation needed before coupling back to the integral
free harmonic lattice.

## Remaining exact gate

Quotienting by `D_p` leaves one binary coordinate for each matched pair, so
its dimension is `(p+1)/2`.  The full audit shows that later filtered Wall
maps collapse almost all of this quotient, but only finite-prime ranks are
currently known.  The next exact task is:

1. express the induced map on the pair-orbit coordinates by a rational
   projective formula;
2. classify its kernel and cokernel for every odd prime;
3. construct a uniformly bounded section on its boundary image.

This is strictly smaller than searching a decoder on all of
`P^1(F_p)`, and it avoids the invalid assumption that arbitrary `SL_3`
coefficient translates preserve one filtered resolution generator.
