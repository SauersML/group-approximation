---
rg: 2
id: nonaffine-source-two-tail-kernel-proof
kind: route
title: Empty pinned kernel would give a forbidden cap-range witness section
target: nonaffine-source-gadgets-force-a-pinned-two-tail-kernel
requires:
  - rstar-two-tail-peeling-reduces-fc-char-to-a-dense-kernel
  - fano-cap-range-sections-cannot-encode-nonaffine-relations
---

Assume the pinned kernel is empty.  Keep an arbitrary visible assignment
`phi in C` fixed and reverse the deletion order.  At each row at most two
coordinates have already been assigned.  The fixed section used in the
two-retained-coordinate lemma extends them through a maximal cap.  The
choices depend only on the already assigned bits, so using the same sections
for every `phi` defines one deterministic pp witness section on all of `C`.
At every target occurrence its range lies in the corresponding fixed cap.

The second prerequisite says that a cap-range witness section for the full
source relation forces that relation to be affine.  This contradicts the
hypothesis on `C`; hence some target row survives peeling.

