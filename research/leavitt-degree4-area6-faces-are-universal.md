---
rg: 2
id: leavitt-degree4-area6-faces-are-universal
kind: claim
title: All 48 reduced area-six identity faces use only the universal corner laws
artifacts:
  - research/leavitt-degree4-area6-universal-faces-proof.md
  - research/artifacts/search-leavitt-degree4-relative-pictures.py
distinct_from:
  leavitt-degree-four-corner-subgroup-is-v4-d8-f4: that proves the arbitrary-word corner embedding; this records the exact reduced area-six topology and its independent universal-normal-form audit.
---

After excluding immediate picture dipoles, the area-six degree-four census has
exactly 48 canonical cyclic coefficient labels that evaluate to the identity.
Every one is already trivial in

```text
[V4(a,b)*C2(c)*C2(d)*C2(e)*Z(p)*Z(r)]^(*4).
```

Their six `(corner count, coefficient-letter count)` shapes are
`(2,2),(4,4),(6,14),(8,16),(10,26),(14,38)`.  No bounded face uses an
additional Leavitt relation or the false target law `[c,d]=1`.
