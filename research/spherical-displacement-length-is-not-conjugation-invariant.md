---
rg: 2
id: spherical-displacement-length-is-not-conjugation-invariant
kind: claim
title: Cloud displacement is subadditive but conjugation invariant only along shadow maps
distinct_from:
  a3-cone-repairs-to-coboundaries-not-cocycles: that identifies which cohomological target the building cone can measure; this identifies which length the cone may be applied to at all, and shows the spherical program's length fails the cone theorem's coefficient hypothesis outright.
  hs-defect-is-mean-square-sphere-displacement: that converts a matrix Hilbert-Schmidt defect into an average pointwise unitary displacement; this is a statement about the permutation-group length itself, its subadditivity, and the exact extent of its conjugation invariance.
  spherical-relation-defect-pairs-small-chord: that bounds the chord between the two discrete outputs of one tested relation; this bounds how a length is distorted when an arbitrary correction is conjugated by a shadow map.
artifacts:
  - research/artifacts/pdf-gluing-calculus-integration-2026-08-23.md
---

**ESTABLISHED.**  Let `x_1,...,x_N` be a cloud on `S^(d-1)` and for
`c in Sym(N)` and `1<=r<=infinity` put

```text
ell_r(c)=((1/N) sum_j ||x_j-x_(c(j))||^r)^(1/r),
ell_infinity(c)=max_j ||x_j-x_(c(j))||.                 (SDL1)
```

This is the geometric locality measure used by
`spherical-short-holonomies-admit-local-gauge`: a correction is admissible
exactly when its `ell_r` is small.

**1. It is a length.**  `ell_r(1)=0`, `ell_r(c^(-1))=ell_r(c)`, and

```text
ell_r(c'c)<=ell_r(c)+ell_r(c').                         (SDL2)
```

Indeed `||x_j-x_(c'c(j))||<=||x_j-x_(c(j))||+||x_(c(j))-x_(c'(c(j)))||`;
take `L^r` of both sides against the uniform counting measure and use
Minkowski, noting that `j |-> c(j)` is measure preserving so the second term
has `L^r` norm exactly `ell_r(c')`.

**2. It is not conjugation invariant, and the failure is maximal.**  For a
uniform iid cloud, all but `o(N)` indices can be greedily paired with another
index at distance `eta(N)->0`, and by
`spherical-tight-single-colour-near-perfect-matching` applied to `U=-I` all
but `o(N)` indices can be paired with an index within `eta(N)` of their
antipode.  Let `c` be the involution swapping the near pairs and let `h` be
any permutation carrying the near-pair structure onto the antipodal-pair
structure.  Then

```text
ell_r(c)<=eta(N)+o(1),
ell_r(h c h^(-1))>=2-o(1),                              (SDL3)
```

for every `r`, including `r=infinity`.  So conjugation can inflate the length
from zero to the full diameter of the sphere.

Consequently `(SDL1)` **does not satisfy the coefficient hypothesis `(AMC5)`
of the metric cone theorem**, which requires `ell(hgh^(-1))=ell(g)` for all
`h` in the coefficient group.  Any attempt to run the `A_3(F_q)` metric cone,
or any other conjugation-invariant-length filling argument, directly on
`Sym(N)` with the cloud displacement length fails at its first hypothesis.
This is independent of, and logically prior to, the coboundary-versus-cocycle
restriction recorded in `a3-cone-repairs-to-coboundaries-not-cocycles`.

**3. It is invariant, up to two matching radii, along shadow maps.**  Suppose
`sigma in Sym(N)` tightly shadows a unitary `U` at radius `rho` off an
exceptional set of density `theta`:

```text
||U x_j-x_(sigma(j))||<=rho    for j outside E,  |E|<=theta N.   (SDL4)
```

Then for every `c in Sym(N)`,

```text
|ell_r(sigma c sigma^(-1))-ell_r(c)|
   <=2 rho+2(2 theta)^(1/r).                            (SDL5)
```

Substituting `j=sigma(i)` turns the left displacement into
`||x_(sigma(i))-x_(sigma(c(i)))||`, and off `E union c^(-1)E`,

```text
||x_(sigma(i))-x_(sigma(c(i)))||
 <=rho+||U x_i-U x_(c(i))||+rho
 =||x_i-x_(c(i))||+2 rho,                               (SDL6)
```

because `U` is an isometry.  Minkowski gives `(SDL5)`; the exceptional term
is bounded by the diameter `2` on a set of density at most `2 theta`.  The
same computation run backwards gives the reverse inequality.

## Consequence for the gauge system

The conjugations that actually occur in the gauge law

```text
c_k=delta_(g,h,k)(sigma_h^(-1)c_g sigma_h)c_h           (SDL7)
```

are exactly conjugations by shadow maps, so by `(SDL5)` each one costs an
additive `2 rho` and nothing multiplicative.  A cone or filling argument for
`(SDL7)` is therefore available only along paths of **bounded** length, and
the admissible bound is fixed by the table, not by the dimension: propagating
a correction across `L` relations costs at most `L` relation-defect radii plus
`2 L rho`.  The obstruction is not the coefficient group's cohomology; it is
whether the fixed table's identities among relations can be filled by boundedly
many shadow-conjugated relation defects.
