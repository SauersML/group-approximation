---
rg: 2
id: atlas-o8plus-canonical-moved-module-completion-fails
kind: claim
title: The canonical Omega8+(2) singular-parabolic overgroup cannot complete either marked Q1920 seam
artifacts:
  - experiments/atlas_a4_q1920_o8p_discovery.g
  - research/artifacts/atlas-a4-q1920-o8plus-seam.json
distinct_from:
  atlas-sp6-canonical-moved-module-completion-fails: that excludes the 2^5:S6 parabolic host in Sp6(2); this excludes the larger singular 2^6:A8 parabolic host in Omega8+(2).
  atlas-q1920-agl5-has-no-collision-involution: that assumes the order-32 module is preserved; this ambient orthogonal group genuinely moves it.
---

The singular-vector stabilizer in `Omega8+(2)` has shape `2^6:A8`.  Its
Levi `A8` has two classes of `A5` subgroups.  The first has three invariant
order-32 submodules and none has the Q1920 module profile.  The second has a
unique invariant order-32 submodule, and it has exactly the required profile

```text
(1,1), (1,2), (15,32), (15,32).                            (O8P-1)
```

This gives one parabolic conjugacy class of the required `Q=2^5:A5`.

Its ambient normalizer has order 7680.  Conjugation induces a subgroup of
order 3840 in `Aut(Q)`, which also has order 7680, so there are exactly two
ambient-inequivalent embedding twists.  Transport both marked Q1920 tuples
through both twists.  The exact profiles

```text
(|C(A)|, collision count, seam count)=(8,0,0),(72,0,0)     (O8P-2)
```

occur for each marking.  Thus the canonical `Omega8+(2)` moved-module host
contains no faithful marked collision involution, before the seam generator
`z` is considered.

This does not exclude nonclassical or higher-rank finite completions.
