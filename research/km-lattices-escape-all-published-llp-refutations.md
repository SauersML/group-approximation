---
rg: 2
id: km-lattices-escape-all-published-llp-refutations
kind: claim
title: Every published mechanism for refuting the local lifting property is vacuous at the simple Kazhdan Kac-Moody lattices
artifacts:
  - research/artifacts/isw-ddjmo-cr-cohomology-sources-2026-08-21.md
  - research/artifacts/km-lattice-cohomology-and-lp-fork-2026-08-23.md
distinct_from:
  twin-lattices-exclude-known-llp-fences: that excludes known LLP-failure GROUPS as subgroups of the lattices; this additionally shows the refutation MECHANISMS themselves cannot fire, including the Ioana-Spaas-Wiersma cohomological machinery published after those fences.
  kac-moody-lattice-is-non-hyperlinear-or-llp-failure: that is the forced-witness dichotomy; this is the evidence audit showing the LLP-failure branch has no known proof mechanism, sharpening the stakes of the dichotomy without deciding it.
  compact-hyperbolic-km-lattices-fail-lp: that pursues the LP (global-splitting) failure through Corollary E's surviving clause; this documents that no such pursuit can reach the LLP.
---

**THEOREM (established; proof in
`km-llp-refutation-vacuity-proof`).**  Let `Lambda` be a simple
Kazhdan Kac-Moody lattice of `simple-kazhdan-kac-moody-lattices-exist`
(e.g. `Lambda_(2,4,6)(q)`, `q > 1764^3`).  Every published route to
refuting the LLP of a full group C*-algebra is unavailable at
`C*(Lambda)`:

```text
(1) Ioana-Spaas-Wiersma Theorem A (arXiv:2006.01874, the only
    published LLP-refuting mechanism beyond subgroup passage):
    VACUOUS -- its condition (3) requires finite-dimensional
    projective representations realizing nontrivial cocycles, and
    every finite-dimensional projective representation of Lambda is
    trivial (Malcev + simplicity, via PU(n) < GL(n^2)).
(2) ISW Corollary D: DEAD -- it refutes only the LP, and its
    hypothesis fails anyway: H^2(Lambda; Z Lambda) = 0
    (km-group-ring-h2-vanishes-for-the-lattices).
(3) ISW Corollary E and the relaxed Theorem A: confined to the LP by
    the paper's own statements; they cannot refute the LLP whatever
    the L^0 computation yields.
(4) Thom's examples and all subgroup/permanence passages: excluded
    by twin-lattices-exclude-known-llp-fences.
```

Consequence: the LLP branch of
`kac-moody-lattice-is-non-hyperlinear-or-llp-failure` is untouched
by all published machinery; deciding it requires either the positive
construction (`triangle-relator-extension-admits-local-ucp-sections`)
or a genuinely new refutation mechanism.  Should the L^0 defect
prove nonzero while LLP holds, `C*(Lambda)` would have the LLP
without the LP.
