---
rg: 2
id: atlas-a5-seam-obstruction-is-not-universal
kind: claim
title: The A5 transported-involution obstruction disappears in every other faithful rectangle image through degree twelve
artifacts:
  - experiments/atlas_a4_large_k22_intersection_screen.g
  - research/artifacts/atlas-a4-large-k22-intersection-screen.json
distinct_from:
  atlas-a5-large-rectangle-cannot-share-marked-collision-seam: that proves the exact incompatibility of the A5 completion; this exhausts the previously known low-index local alternatives and shows that their two radial S3 subgroups instead intersect trivially.
  atlas-large-k22-has-faithful-a5-completion: that records the orders of twelve faithful local coset images; this classifies the transported radial intersections and their compatibility with the marked collision involution.
---

Among all faithful large-rectangle coset images of degree at most twelve, the
transported-involution obstruction is exact for the four `A5` images and for
no others.

The complete census is

```text
image order 60:    4 images, radial S3 intersection C2,
                   its B-label is the noncentral collision transposition;

image order 168:   6 images, radial S3 intersection trivial;

image order 1920:  2 images, radial S3 intersection trivial.             (LI-1)
```

Thus all four `A5` images are excluded by
`atlas-a5-large-rectangle-cannot-share-marked-collision-seam`, while all
eight non-`A5` images survive this exact intersection test.  In particular
there can be no universal identity equating a nontrivial word in the two
radial `S3` subgroups: the order-168 and order-1920 images are exact finite
counterexamples.

This is a bounded local classification, not a common-frame completion.  A
surviving local image must still be amalgamated simultaneously with the
marked `S3 x S3`, collision `S4`, and forward `C144` vertices.
