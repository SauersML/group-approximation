---
rg: 2
id: atlas-k22-intersection-census-proof
kind: route
title: Enumerate the faithful low-index rectangle actions and compare their radial intersection with the collision centralizer
target: atlas-a5-seam-obstruction-is-not-universal
requires:
  - atlas-a5-large-rectangle-cannot-share-marked-collision-seam
  - atlas-large-k22-has-faithful-a5-completion
artifacts:
  - experiments/atlas_a4_large_k22_intersection_screen.g
  - research/artifacts/atlas-a4-large-k22-intersection-screen.json
---

The GAP verifier uses the same local four-generator presentation and complete
`LowIndexSubgroupsFpGroup` list through index twelve as the original A5
certificate.  It retains an action exactly when both marked `S3` subgroups
have order six and all four marked `A4` edge subgroups have order twelve.

For every retained action it forms

```text
A=<r,u>,             B=<t,s>,
t=y^-1,              s=b t^-1,
I=A intersect B.
```

The collision calibration independently fixes `J=S4` and lists the three
involutions of `B`.  Exactly one is centralized by the marked collision
double transposition `c`; the flags are `[false,true,false]`.  If `I` is
trivial, the transported-intersection test is vacuous.  If `|I|=2`, the
verifier locates its generator in this marked list and tests the corresponding
flag.

All twelve retained actions are classified by exact permutation closure.
The four order-60 actions use label three and fail.  Each of the six
order-168 and two order-1920 actions has `I=1`, proving `(LI-1)` and the
claimed finite counterexamples to any universal radial-intersection identity.
