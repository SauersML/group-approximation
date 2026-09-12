---
rg: 2
id: atlas-a4-19243-classical-collapse
kind: claim
title: The shortest A4 packet plus 19243 excludes every regular A8 automorphism alignment
artifacts:
  - experiments/atlas_triangle_19243_packet.py
distinct_from:
  atlas-seven-word-a9-a10-exclusion: that excludes two larger alternating-group overmodel geometries with a seven-word packet; this claim exhausts the entire inner/outer automorphism alignment sector of the two regular A8 charts and exposes a local-A4 mechanism.
  atlas-19243-s3-relative-normal-form: collision 19243 alone has an exact regular-margin S4 model; the present claim uses the shortest boundary triangle packet jointly with it.
---

Consider the two regular `A8` chart actions with their relative position an
automorphism intertwiner.  Every automorphism of `A8 ~= GL_4(F_2)` is inner or
inner followed by the outer involution

```text
theta(g)=(g^-1)^T.
```

Among the `20160` inner alignments, exactly `30` satisfy all thirty relations
in `atlas-shortest-a4-triangle-packet`; among the `20160` outer alignments,
exactly `30` do so.  None of these sixty surviving alignments also satisfies
collision `19243`.

Hence the fixed mixed packet

```text
{ thirty shortest X-length-nine A4 pair-cubes } union { q_19243 }
```

has no zero-defect model anywhere in the full `40320`-element classical
automorphism sector.

The significance is structural rather than merely enumerative.  The triangle
relations first force overlapping local regular-`A4` joint types; collision
`19243`, which by itself admits an exact `S4` regular-margin realization, then
kills every way those local types can be glued by an automorphism of the ambient
regular `A8` chart.  Any remaining zero/low-energy model must therefore use
genuinely nonclassical multiplicity mixing.
