---
rg: 2
id: gottschalk-via-matrix-observable-extension
kind: route
title: A unital matrix extension cannot annihilate a missing output cylinder
target: gottschalk-surjunctivity-conjecture
requires:
  - split-ca-quantization-has-sharp-defect
  - injective-ca-pullbacks-extend-to-matrix-observables
artifacts:
  - research/artifacts/gottschalk-quantum-compression-2026-09-07.md
---

Finite groups are settled by counting. For an infinite G, an injective
finite-alphabet CA has a local decoder by compactness and extension of
the inverse coordinate rule. The open extension premise supplies a
unital homomorphism on the full quasilocal matrix algebra. By the
established matrix-unit obstruction, such an extension exists only if
the encoder is onto. This proves the goal conditionally.

The extension premise is still open. The local completely positive
compression constructed in the artifact does not discharge it.

The route is valid, but its open premise is equivalent to the target
(2026-09-12). The converse route is
`matrix-observable-extension-from-surjunctivity`, and the two routes form
a deliberate cycle. `injective-ca-product-trace-zero-one-law` shows the same
for every trace-level weakening of the premise, automaton by automaton.
Progress here therefore needs a per-site logarithmic invariant, not a
different operator extension.
