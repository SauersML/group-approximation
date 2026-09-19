---
rg: 2
id: atlas-first-noncentral-core-cycle-is-spherical-triangle-proof
kind: route
title: Absorb collision and the first core edge, then compute local angles
target: atlas-first-noncentral-core-cycle-is-spherical-triangle
requires:
  - atlas-19243-s3-relative-normal-form
  - atlas-forward-collision-bass-serre-reduction
---

Use `y=t^-1` and let `u` be the involution introduced by the first additional
core edge.  Choose the exact noncentral collision branch from
`atlas-19243-s3-relative-normal-form`:

```text
J=<t,s,c> ~= S4,       K=<t,s> ~= S3,
<c,t> ~= A4.                                             (TRI-1)
```

The first core cube is `(u t^-1)^3=1`.  Together with `u^2=t^3=1` it can be
absorbed into

```text
H=<u,t> ~= A4.                                           (TRI-2)
```

On the first chart side the four relevant packet letters form

```text
F'=<r,z,c,u> ~= S3 x S3,
<c,u> ~= C2 x C2.                                       (TRI-3)
```

The three finite vertices and their edge groups are therefore

```text
F' --<c>-- J --<t>-- H --<u>-- F'.                      (TRI-4)
```

For a triangle of groups, the angle at a vertex is `2*pi/m`, where `m` is the
shortest alternating syllable length in the kernel of the free product of the
two incident edge groups mapping to that vertex.

* At `F'`, commuting involutions give the shortest kernel word `(cu)^2`, of
  syllable length four, hence angle `pi/2`.
* At `J`, the marked `C2` and `C3` generate `A4`; the triangle relation
  `(ct)^3` has syllable length six, hence angle `pi/3`.
* At `H`, the same `(2,3,3)` calculation gives angle `pi/3`.

Thus

```text
angle(F')+angle(J)+angle(H)=pi/2+pi/3+pi/3=7pi/6>pi.     (TRI-5)
```

The non-spherical Gersten--Stallings developability criterion is therefore
inapplicable.  This calculation also explains why regular tree-amalgam
constructions stop exactly here: all three edge embeddings are individually
injective, but closing their first cycle creates positive curvature.
