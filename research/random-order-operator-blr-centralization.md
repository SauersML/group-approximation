---
rg: 2
id: random-order-operator-blr-centralization
kind: route
title: Dead — average randomized coordinate products and apply unitary BLR self-correction
target: multiplicity-space-centralization-after-code-block-pinching
requires:
  - unitary-blr-average-self-corrects-uniformly
---

**Dead.**  The proposed construction assigns to every binary label an
ordered product of the multiplicity-space coordinate reflections, choosing
the order randomly to spread the cost of swaps.  One then hopes that complete
pair energy and all-local-dual parity energy bound the average BLR defect,
after which amenable averaging/polarization and
`unitary-blr-average-self-corrects-uniformly` would produce an abelian table.

`sparse-pauli-pair-defeats-random-order-blr` invalidates the required first
step.  A single Pauli pair has vanishing balanced presentation energy but
constant ordered-table BLR defect for every deterministic or randomly chosen
ordering table.  Averaging over order before polarization makes the two
orders cancel exactly on a quarter of the labels, producing a singular mean
at constant distance from the raw products.

The residual design rule is precise: apply all-local-dual sparse-tail repair
before expanding coordinate words into a full BLR table.  Random ordering
cannot itself perform that repair, because one sparse anticommuting pair is
sampled with constant probability by a uniform full-table label.

