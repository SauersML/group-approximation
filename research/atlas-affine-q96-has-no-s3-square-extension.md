---
rg: 2
id: atlas-affine-q96-has-no-s3-square-extension
kind: claim
title: The natural affine Q96 has no marked S3-square extension in AGL5(2)
artifacts:
  - experiments/atlas_a4_agl5_q96_exact_screen.g
  - research/artifacts/atlas-a4-agl5-q96-exact-screen.json
distinct_from:
  atlas-forward-core-triangle-has-faithful-q96-completion: that constructs the abstract order-96 triangle; this excludes one explicit natural affine embedding from the next S3-square vertex.
  atlas-q96-to-c144-cycle-is-six-generator-finite-vertex-test: that asks for any finite quotient preserving all four vertices; this is an exhaustive ambient calculation for one marked AGL5(2) carrier only.
  atlas-one-forward-c3-has-no-standard-gl6-completion: that excludes a two-coordinate-padded standard binary chart; this starts from the new noncentral Q96 triangle and exhausts its affine five-dimensional ambient group.
---

Fix the affine realization of the certified `Q96=<c,u,t>` in
`AGL_5(F2)` used by the balanced-square search.  The ambient group has order

```text
|AGL5(2)|=319979520.
```

To extend `Q96` to the marked vertex

```text
F'=<r,z,c,u> ~= S3 x S3,
```

one needs, in particular,

```text
r in C_G(c),   ord(r)=3,   u r u=r^-1,
z in C_G(u),   ord(z)=3,   c z c=z^-1.                 (AGL5-Q96-1)
```

Exact centralizer enumeration over the whole ambient group gives

```text
#{r satisfying (AGL5-Q96-1)}=0,
#{z satisfying (AGL5-Q96-1)}=0.                       (AGL5-Q96-2)
```

As a calibration, the independent collision-side transporter calculation
finds four involutions `s` extending `<c,t>` to the required marked `S4` and
killing `q_19243`.  Thus the empty order-three fibers are not caused by a
failed ambient or `Q96` construction.

Consequently this fixed affine `Q96` cannot absorb even the `S3 x S3` vertex,
and therefore cannot reach the subsequent 144-state double attachment.  This
is exact for every element of `AGL5(2)`, but only for the displayed conjugacy
class of marked affine `Q96`; it is not an all-finite-carrier obstruction.
