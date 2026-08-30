---
rg: 2
id: higher-whitehead-universal-finitely-presented-torsion-free-group
kind: claim
title: One finitely presented torsion-free group injects all connective Whitehead groups
distinct_from:
  whitehead-universal-finitely-presented-torsion-free-group: that records only ordinary Wh=Wh_1; this strengthens the particular constructed witness simultaneously in every connective Whitehead degree.
---

There exists a fixed finitely presented torsion-free group `U` such that
every countably generated recursively presented torsion-free group `K`
admits an embedding

```text
K -> U
```

for which

```text
Wh_i(K) -> Wh_i(U)
```

is injective for every `i>=0`, simultaneously for the same embedding.

Here `Wh_i(G)=pi_i Wh_Z(G)` is Waldhausen's connective Whitehead group.
In particular `Wh_0` is the reduced projective class group and `Wh_1`
is the ordinary Whitehead group.

**ESTABLISHED 2026-08-30** by
[[higher-whitehead-universal-group-via-the-two-hnn-edges]].
