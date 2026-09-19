---
rg: 2
id: atlas-a10-natural-padding-fails-next-core-edge
kind: claim
title: Every naturally padded A10 forward-collision carrier fails the next core edge
artifacts:
  - experiments/atlas_a4_a10_first_chart_extension.g
  - experiments/atlas_a4_a10_next_core_overgroup.g
  - research/artifacts/atlas-a4-a10-next-core-natural-padding.json
distinct_from:
  atlas-forward-collision-has-faithful-a10-quotient: that supplies the faithful minimal carrier; this proves that the carrier cannot absorb the next large-component core edge inside its natural permutation representation or any trivial-point padding of it.
  atlas-one-forward-c3-has-no-standard-gl6-completion: that excludes a standard binary-linear chart in dimension six; this is an all-padding theorem for one explicit alternating permutation carrier.
  atlas-a4-collision-assisted-opaque-star-compiler: that needs an obstruction for arbitrary complex regular multiplicity; this only fences the natural permutation overgroup of the A10 carrier.
---

Use the degree-ten `A10` certificate of
`atlas-forward-collision-has-faithful-a10-quotient`.  Put

```text
F=<r,z,c> ~= C3 x S3,
```

and let `u` be the missing first-chart involution which completes the first
large rank-three support.  Its exact support relations and the next core edge
are

```text
u^2=1,       u r u=r^-1,       [u,z]=[u,c]=1,
(u t^-1)^3=1.                                             (A4-NEXT-1)
```

There is no `u in S_d` satisfying `(A4-NEXT-1)` when the displayed `A10`
acts naturally on ten points and fixes the remaining `d-10` points, for any
`d>=10`.

In degree ten the statement is an exact finite transporter calculation.  The
canonical first-chart `F` has twelve extensions to the natural pointwise-two-
point-stabilizer `A8`; every extension has core mask `0x1`: it satisfies the
already imposed edge `r^-1 -> b` and none of the other three large-component
edges.  Directly, among the twelve involutions satisfying the first four
relations in `(A4-NEXT-1)`, none satisfies the last.

The padding statement is not an extrapolation from the finite screen.  In the
natural degree-ten action, `F` has one nontrivial orbit of size eight and
fixed-point set `{1,8}`.  After padding, its fixed-point set is

```text
T={1,8,11,...,d}.
```

The first four relations make `u` normalize `F`, so `u` preserves `T`.
The element `t` fixes `T` pointwise.  On `T`, the last relation therefore
says `u^3=1`; together with `u^2=1` it forces `u|_T=1`.  The problem reduces
exactly to the degree-ten calculation on the eight-point nontrivial orbit.

This is the first failed extension of the explicit A10 point model, but it is
not yet a regular-multiplicity obstruction.  The next valid object is the
small triangle completion with vertices

```text
H=<F,u> ~= S3 x S3,
J=<F,t> ~= C2^4 : (C3 x S3),
<u,t> ~= A4,
```

of orders `36,288,12` respectively.
