---
rg: 2
id: atlas-q1920-agl5-has-no-collision-involution
kind: claim
title: No completion preserving the self-centralizing Q1920 module can contain the marked collision involution
artifacts:
  - experiments/atlas_a4_q1920_agl5_seam.g
  - research/artifacts/atlas-a4-q1920-agl5-seam.json
distinct_from:
  atlas-q1920-holomorph-has-no-collision-involution: that assumes the collision element normalizes the whole marked Q; this allows Q to move and assumes only that its characteristic module V remains normal and self-centralizing.
  atlas-q1920-seam-has-no-low-index-action: that is a bounded permutation-action census; this exhausts the full affine normalizer of V, whose order is 319979520.
---

Let `V ~= C2^5` be the characteristic module of either marked `Q1920`, and
let `A=<r,u>`.  Choose an `A`-containing `A5` complement and use the action
of `Q` on its 32 cosets.  Then `V` acts regularly, so its full permutation
normalizer is

```text
N_Sym(32)(V) = Hol(V) = AGL5(2),       |AGL5(2)|=319979520.   (AGL5-1)
```

The pointwise centralizer of `A` in this affine normalizer has order twelve,
with seven involutions.  For every one of those involutions `c`, direct
evaluation of

```text
(c t)^3,             t c s c t^-1 c s t c                 (AGL5-2)
```

finds that at least one word is nontrivial.  This holds for both marked
Q1920 classes.  Hence no marked collision involution, and therefore no
faithful seam `S3=<c,z>`, occurs in `Hol(V)`.

Consequently, if a finite completion `L` keeps `V` normal and
`C_L(V)=V`, it cannot exist: the standard conjugation embedding of a group
with normal self-centralizing abelian subgroup places `L` inside `Hol(V)`,
contradicting `(AGL5-2)`.  Any surviving completion must move `V` or satisfy
`C_L(V)>V`.
