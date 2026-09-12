---
rg: 2
id: atlas-fourteen-shifted-tangent-spaces-have-an-s3-flat
kind: claim
title: The fourteen shifted A4 tangent spaces share a 3360-dimensional S3 flat
artifacts:
  - experiments/atlas_a4_core_tangent_transversality.py
distinct_from:
  atlas-fourteen-edge-core-has-no-collision-to-c6-path: that fences incidence-path telescoping; this works directly with the literal common-U shifted double cosets and gives an explicit infinitesimal common direction.
  atlas-a4-two-c3-line-carriers-have-exact-angle-gap: that gives a positive angle after a common collision vector reaches both C3 carriers; this shows the packet double-coset geometry alone has a much larger flat kernel before that nonlinear collision coupling.
---

Let `R` be the frozen reference alignment and let `D_e` run through the eight
distinct shifted double-centralizer sets underlying the fourteen-word core.
Right-translate tangent vectors at `R` to the identity.  If the factor-one and
factor-two endpoints of `e` are `g_(e,1),g_(e,2)`, the complexified tangent
space is

```text
S_e = Fix(Ad rho(g_(e,1)))
      +Fix(Ad rho(R g_(e,2) R^-1)).                    (A4-TAN-1)
```

There is a choice `l_e` of one of the two displayed endpoints for every one
of the eight edges such that

```text
L=<l_e:e> ~= S3.                                       (A4-TAN-2)
```

The exact selected endpoint matrices are

```text
01000000000101000000010000000001
01000000000001000001010000000001
01000000000100000001010000000001
01000000000101000001000000000001
```

(the eight-edge list repeats these four matrices once).  Consequently

```text
Fix(Ad rho(L)) subseteq intersection_e S_e.            (A4-TAN-3)
```

On each relative matrix-unit coordinate of `Reg(A8)`, this supplies

```text
[A8:L]=20160/6=3360
```

common tangent dimensions.  It is strictly larger than the `H=GL3(2)`
commutant direction: for example, on the diagonal relative coordinate,

```text
T=i 1_(ell2(L))
```

is skew-Hermitian and fixed by every selected `l_e`, hence lies in every
`S_e`, but it is not fixed by left `H` because `|H|=168>|L|`.

Therefore no dimension-free *linearized packet transversality* inequality

```text
dist_2(T,rho(H)') <= C (sum_e dist_2(T,S_e)^2)^1/2     (A4-TAN-4)
```

can hold: the right side is zero on this explicit `T` and the left side is
positive.  Alternating projections or conditional expectations onto the
fourteen packet tangent sums cannot by themselves force the common frame into
the `H` commutant.

This does not refute the nonlinear joint packet--collision estimate
`(A4-C3-9)`.  The reference packet point `R` is not a zero of collision
`19243`, and the collision derivative has not been imposed on `(A4-TAN-3)`.
It proves that collision must remove an exact `S3` tangent flat, rather than
merely pay the already-computed `H_6`--`K` principal-angle gap.
