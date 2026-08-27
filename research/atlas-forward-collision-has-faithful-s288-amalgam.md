---
rg: 2
id: atlas-forward-collision-has-faithful-s288-amalgam
kind: claim
title: The minimal forward-collision quotient embeds all three vertex groups in a finite S288 target
artifacts:
  - experiments/atlas_a4_regular_amalgam_finite_search.py
  - research/artifacts/atlas-a4-forward-collision-s288-amalgam.json
  - research/atlas-forward-collision-has-faithful-s288-amalgam-proof.md
distinct_from:
  atlas-forward-collision-bass-serre-reduction: that isolates the finite-quotient vertex-injection question; this answers it positively by an explicit regular-representation amalgam.
  atlas-one-forward-c3-has-no-standard-gl6-completion: that rules out one fixed standard binary-linear chart; this finite permutation target is nonstandard and preserves every vertex group exactly.
  atlas-a4-collision-assisted-opaque-star-compiler: that needs a global full-packet matrix obstruction; this proves the minimal forward-collision subset cannot supply one by itself.
---

For the group `Gamma` of `atlas-forward-collision-bass-serre-reduction`, there
is a homomorphism

```text
Gamma -> Q <= S_288
```

whose restrictions to

```text
F ~= C3 x S3,       C ~= C2^4 semidirect C3^2,
K ~= S3
```

are injective.  Their image orders are respectively `18,144,6`; in
particular the shared involution `b=s t` survives.

The construction is exact.  It realizes `C` as `A4 x A4`, adjoins the factor
swap as the collision involution `c`, and glues this order-288 group to
`S3 x C2` over the common labeled `V4=<b,c>` using their regular permutation
representations.  The collision relation then reduces inside the second
factor to the ordinary `S3` identity `t s t^-1 s t=1`.

Thus the minimal forward-collision support has compatible finite regular
models and cannot by itself force `b=1` or a positive Hilbert--Schmidt gap.
