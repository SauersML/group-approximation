---
rg: 2
id: atlas-sp6-canonical-moved-module-completion-fails
kind: claim
title: The canonical Sp6(2) parabolic overgroup cannot complete either marked Q1920 seam
artifacts:
  - experiments/atlas_a4_q1920_sp6_seam.g
  - research/artifacts/atlas-a4-q1920-sp6-seam.json
distinct_from:
  atlas-any-q1920-completion-must-move-the-module: that forces a completion outside every group normalizing V; this tests and excludes the canonical rank-two Lie group which moves the parabolic module.
  atlas-q1920-agl5-has-no-collision-involution: that works inside the affine normalizer of V; Sp6(2) genuinely moves V, so this is a new overgroup layer.
---

In `Sp6(2)`, a nonzero-vector stabilizer has shape `2^5:S6`.  Its Levi
`S6` has two classes of `A5` subgroups.  Exactly one class gives the
elementary-abelian module orbit/span profile of the marked Q1920 groups:

```text
(1,1), (1,2), (15,32), (15,32).                           (SP6-1)
```

Thus there is a unique canonical parabolic slice `Q=2^5:A5` of the required
module type.

To remove dependence on a chosen abstract isomorphism, compute
`Aut(Q)` and quotient it by the automorphisms induced by
`N_Sp6(2)(Q)`.  Their orders are respectively 7680 and 1920, leaving exactly
four embedding twists.  For each of the two marked Q1920 tuples and all four
twists, compute the pointwise centralizer of the transported `A=<r,u>` and
test every involution against the faithful collision relations.

The eight exact profiles are

```text
(|C(A)|, collision count, seam count)
   = (4,0,0) twice and (12,0,0) twice, for each marking.   (SP6-2)
```

Hence neither marked seam embeds in the canonical `Sp6(2)` moved-module
completion.  This is not a classification of all finite groups containing
two moved conjugates of `V`.
