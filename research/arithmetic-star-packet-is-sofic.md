---
rg: 2
id: arithmetic-star-packet-is-sofic
kind: claim
title: The arithmetic star-packet carrier is a finitely presented sofic non-MF group
distinct_from:
  arithmetic-star-packet-non-mf: That proves operator-norm non-MF by packet collapse; this proves the same carrier is nevertheless sofic and therefore hyperlinear.
  arithmetic-star-packet-fiber-clique-action-sofic: That supplies the graph-action input; this embeds the entire amalgam into the resulting graph wreath product.
artifacts:
  - notes/FINITE_PACKET_SELF_COPY_COLLAPSE.md
  - notes/ARITHMETIC_STAR_PACKET_HYPERLINEAR_AUDIT.md
  - research/artifacts/sofic-halo-permanence-falsification-audit-2026-08-20.md
---

The group

```text
W=(S_9 rtimes P) *_P E
```

from `arithmetic-star-packet-carrier` is sofic.  More precisely it embeds in
the graph wreath product of `K=S_9` over the finite-fiber clique graph
`E/ker(theta)`, acted on by the ascending HNN group `E`.

The actor `E` is sofic, the finite vertex group `K` is sofic, and
`arithmetic-star-packet-fiber-clique-action-sofic` supplies the required
sofic graph action.  Graph-wreath sofic permanence therefore makes the
envelope sofic, and subgroup heredity makes `W` sofic.  In particular `W` is
hyperlinear, so it cannot witness `non-hyperlinear-group`.

Combined with `arithmetic-star-packet-non-mf`, this identifies the correct
status of the construction:

```text
finitely presented + sofic + hyperlinear + not operator-MF.
```

