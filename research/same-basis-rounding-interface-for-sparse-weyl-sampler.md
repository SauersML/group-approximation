---
rg: 2
id: same-basis-rounding-interface-for-sparse-weyl-sampler
kind: claim
title: Round same-basis occurrence tests to one PVM without dimension loss
distinct_from:
  bounded-degree-entangled-agreement-pauli-metapixel: that is the complete mixed X/Z metapixel; this isolates its same-basis input.
---

OPEN.  Construct a bounded-degree, bounded-template, perfect-completeness
same-basis occurrence test with the following same-Hilbert conclusion.
From value at least `1-epsilon`, round all X occurrences (and separately all
Z occurrences) to one exact additive `F_2^n` action on a common marked
carrier, equivalently to one spectral PVM, with total squared normalized-HS
change at most

```text
C epsilon^theta
```

for constants independent of `n`, answer count, and ambient dimension.
The rounding may discard at most `C epsilon^theta` marked mass but may not
use a context-dependent family of PVMs, an equality fiber, or a flexible
dimension enlargement.

This is the exact input needed before
`sampled-weyl-defect-controls-common-pvm-dirichlet-energy`.  Ordinary dense
BLR supplies the algebraic conclusion but its complete pair table is not a
finite-template small-cancellation incidence object.  Equality-cloud degree
reduction recreates the known two-pair contour obstruction.

All downstream mixed-incidence issues are now discharged for the private
sampler.  `private-random-weyl-sampler-forces-growing-matrix-dimension` gives
the same-Hilbert matrix-valued dimension floor once the two additive actions
are exact; `private-matching-free-product-separates-pauli-signs` places every
mixed sign test as a constant-area conjugate with no mixed contour; and
`private-weyl-samplers-admit-recursive-selection` computes the finite label
lists.  Consequently this node is the sole analytic/finite-presentation gate
on that route.  In particular no extra relative-small-cancellation,
pair-holonomy, or random-sample-effectivity lemma should be added downstream.

## Attempts

- **Dense BLR.**  Robust but its complete additive-triple incidence is not
  directly compatible with the bounded-template placement gate.
- **Expander equality clouds.**  They synchronize copies through repeated
  equality fibers and recreate short balanced contours.
- **One private port per equality cloud.**  Removing repeated mixed pairs
  removes those contours, but not rooted dilution.
  `bounded-degree-clouds-have-logarithmic-root-gauge-leak` gives exact local
  two-dimensional packets whose conjugation gauge changes by only
  `O(1/log m)` across every cloud edge, while the designated mixed port stays
  a constant distance from the bulk PVM.  Hence even maximum edge-defect
  control does not yield a uniform rooted decoder.
- **Constant-size private basins.**  This geometric interface is positive.
  `constant-size-private-basins-give-uniform-root-control` gives a direct
  same-Hilbert path estimate, preserves mixed degree one, and uses only
  `O(K)` vertices for `K` selected ports.  It forces the additive layer to
  use bounded occurrence on the selected labels themselves; dense BLR
  degree reduction has growing basin size and cannot use the lemma.  The
  remaining positive target is now
  `bounded-occurrence-private-sampler-additive-decoder`, with route
  `constant-private-basins-reduce-same-basis-to-selected-code`.
- **Separate local roundings.**  These do not produce the common PVM needed
  for `(SW2)` and leave a coupling escape.
- **Metric-entropy sparsification of BLR itself.**  This cannot reuse the
  entropy argument which sparsified Weyl energy after exact additivity.
  `subexponential-blr-sampling-has-scalar-contextual-escape` proves that any
  `m` scalar parity/BLR checks on `K` selected labels, even with arbitrary
  auxiliary signs, leave an extendible table space of dimension at least
  `K-m`.  If `m+n<K/8`, it contains a zero-defect table more than `1/4`-far
  from every character restriction.  Exact-PVM metric entropy is therefore
  unavailable until a separate structured tester or actor has already
  confined the raw table.
