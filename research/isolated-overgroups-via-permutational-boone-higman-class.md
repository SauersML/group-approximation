---
rg: 2
id: isolated-overgroups-via-permutational-boone-higman-class
kind: route
title: Quasi-linear groups embed in finitely presented simple groups, and those are isolated
target: linear-and-metabelian-groups-embed-in-isolated-groups
requires:
  - quasi-linear-groups-satisfy-permutational-boone-higman
  - fg-metabelian-groups-embed-in-products-of-coprimary-quotients
  - fp-simple-groups-are-isolated
---

Let `G` be finitely generated and embedded in a finite product of general
linear groups over fields.
- By `quasi-linear-groups-satisfy-permutational-boone-higman`, `G` embeds in a
  finitely presented simple group `S`.
- By `fp-simple-groups-are-isolated`, `S` is isolated.

So `G` embeds in an isolated group.

A finitely generated linear group over a field is the case `r = 1`. A finitely
generated metabelian group embeds in such a finite product by
`fg-metabelian-groups-embed-in-products-of-coprimary-quotients`, as that node's
consumer `quasi-linear-groups-satisfy-permutational-boone-higman` records. A
finitely generated subgroup of a finite product of `GL`'s is again a finitely
generated group of the same kind.
