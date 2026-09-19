---
rg: 2
id: atlas-q168-rectangles-collapse-fj-seam
kind: claim
title: Every faithful order-168 rectangle class through degree twelve universally collapses the F/J seam
artifacts:
  - experiments/atlas_a4_non_a5_fj_colimits.g
  - research/artifacts/atlas-a4-q168-fj-colimits.json
distinct_from:
  atlas-a5-large-rectangle-cannot-share-marked-collision-seam: that uses one transported intersection element to exclude the A5 completion; these order-168 rectangles have trivial radial intersection, yet their exact universal colimits still kill both seam generators.
  atlas-a5-seam-obstruction-is-not-universal: that proves the simple A5 intersection mechanism disappears in the order-168 classes; this computes the whole three-vertex colimit and finds a stronger global collapse.
  atlas-full-large-no-simple-quotient-under-million: that excludes targets of bounded order; this is an exact universal-colimit calculation with no ambient-target bound for each marked local class in the census.
---

There are six faithful order-168 large-rectangle coset images in the complete
degree-at-most-twelve census.  For each marked image `Q=<r,y,u,b>`, freeze its
entire multiplication table and form the universal colimit with generators
`z,c` and relations making

```text
F=<r,z,c,u> ~= S3 x S3,        J=<t,s,c> ~= S4,
t=y^-1,                        s=b y.                    (Q168-COL-1)
```

In every one of the six cases the colimit has the exact profile

```text
|colimit|=168,       |image(Q)|=168,
|image(F)|=6,        |image(J)|=6,
image(z)=image(c)=1.                                  (Q168-COL-2)
```

Thus `Q` embeds, but the universal seam relations add nothing to it: they
kill both generators of the second `S3` factor and collapse collision `S4`
to its marked `S3`.  None of the six marked order-168 local completions can
occur in a faithful common-frame carrier, in any ambient group.

This exhausts the order-168 classes only within the degree-at-most-twelve
local census.  The two order-1920 classes in that census require a separate
colimit calculation, and the universal four-relator rectangle may have
higher-index finite completions.
