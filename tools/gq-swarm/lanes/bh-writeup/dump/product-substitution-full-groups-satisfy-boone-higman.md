---
rg: 2
id: product-substitution-full-groups-satisfy-boone-higman
kind: claim
title: The topological full group of a product of primitive aperiodic substitution subshifts, with its Z^d action, embeds in a finitely presented simple group
distinct_from:
  substitution-subshift-full-groups-satisfy-boone-higman: that is one substitution subshift and its Z-action; this is the Z^d-action on a product of d of them, whose full group is much larger than the product of the factor full groups.
artifacts:
  - research/artifacts/gq-bh-bh-free-03-substitution-full-groups.md
---

**ESTABLISHED** by `product-substitution-full-groups-satisfy-boone-higman-proof`
(lane proof, not independently reviewed). No priority is claimed.

**Statement.** Let `tau_1, ..., tau_d` be primitive aperiodic substitutions with
subshifts `(X_i, S_i)`. Let `Z^d` act on `X = X_1 × ... × X_d`, with the `i`-th
generator acting by `S_i` on the `i`-th factor. Then the topological full group
`[[Z^d ↷ X]]` embeds in a finitely presented simple group. This is the group of
homeomorphisms `h` of `X` with `h(x) = S^{n(x)} x` for a continuous `n : X -> Z^d`.

**Consequences.**
- The product `[[S_1]] × ... × [[S_d]]` and all its subgroups satisfy BH.
- `quadratic-rectangle-exchange-groups-satisfy-boone-higman`: rectangle (box)
  exchange groups with quadratic-irrational coordinate data satisfy BH.

**Printed questions.** None located. A grep of the Kourovka Notebook, 21st edition
TeX, for interval exchange, full group, amenable and Cantor found nothing, and so did
the bh-lit list of the BBMZ survey and the BBMZ-hyperbolic questions.
