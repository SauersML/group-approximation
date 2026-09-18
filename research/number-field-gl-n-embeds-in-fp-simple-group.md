---
rg: 2
id: number-field-gl-n-embeds-in-fp-simple-group
kind: claim
title: For every number field K and every n >= 2, GL_n(K) embeds in a finitely presented simple group
distinct_from:
  gl-n-q-embeds-in-fp-simple-group: that is the case K = Q, which the survey asks; this is every number field. The two are equivalent, by restriction of scalars in one direction and K = Q in the other.
  algebraic-linear-groups-satisfy-boone-higman: that is the finitely generated subgroups of GL_n(K); this is the whole countable group GL_n(K).
artifacts:
  - research/artifacts/gq-gq-transfer-consequences.md
---

**OPEN.** For every number field `K` and every `n >= 2`, the countable group
`GL_n(K)` embeds in a finitely presented simple group.

It is equivalent to `gl-n-q-embeds-in-fp-simple-group`.
- The case `K = Q` is that claim.
- Conversely, route `number-field-gl-n-via-gl-n-q` gives this claim from it
  through `number-field-linear-groups-embed-in-gl-n-q`.

No printed source asks this form; it is recorded as a transfer.

## Attempts

None beyond the transfer route.
