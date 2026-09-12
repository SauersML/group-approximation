---
rg: 2
id: central-pullback-finite-image-center-criterion
kind: claim
title: A finite central residual mark survives a pullback whose kernel images have no central p-torsion
artifacts:
  - research/artifacts/rips-central-pullback-finite-image-centers-2026-09-12.md
distinct_from:
  finite-central-extension-rf-iff-virtually-splits: that characterizes residual finiteness of one central extension through virtual splitting; this transports a specified residual mark through a second extension using centers of finite kernel images.
---

Let `p` be a prime. Suppose

```text
1 -> A -> E -> Q -> 1,
1 -> N -> G -> Q -> 1
```

are exact, `A` is finite and central in `E`, and `z in A` has order `p`
and lies in the finite residual of `E`. Assume that the center of every
finite homomorphic image of `N` has order prime to `p`.

Then the fiber product `P=E x_Q G` contains the nonidentity central element
`(z,1)` of order `p` in its finite residual. If `G` is word-hyperbolic,
then `P` is word-hyperbolic and is not virtually torsion-free.

The hypothesis on `N` is inherited from any group mapping onto `N`. It
allows nontrivial finite images, including images of order divisible by `p`.
