---
rg: 2
id: same-basis-rounding-interface-for-sparse-weyl-sampler
kind: claim
title: Round same-basis occurrence tests to one PVM with bounded dimension loss
distinct_from:
  bounded-degree-entangled-agreement-pauli-metapixel: that is the complete mixed X/Z metapixel; this isolates its same-basis input.
---

OPEN.  Construct a bounded-degree, bounded-template, perfect-completeness
same-basis occurrence test with the following bounded-flexible conclusion.
From value at least `1-epsilon`, round all X occurrences (and separately all
Z occurrences) to one exact additive `F_2^n` action on a common marked
carrier in a Hilbert space of dimension at most `K` times the original
dimension, equivalently to one spectral PVM, with total squared normalized-HS
change from the padded occurrence tuple at most

```text
C epsilon^theta
```

for constants `K,C,theta` independent of `n`, answer count, and ambient
dimension.
The rounding may discard at most `C epsilon^theta` marked mass but may not
use a context-dependent family of PVMs or an equality fiber.  Unbounded or
instance-dependent enlargement is not allowed.

Bounded flexibility is sufficient for the terminal argument.
`private-random-weyl-sampler-forces-growing-matrix-dimension` holds uniformly
for exact additive actions of dimension at most `K r` for every fixed `K`,
and `occurrence-local-dimension-games-force-mark-collapse` already permits
extracted strategies of dimension `C_0d`.  Choosing the sampler rank after
the original matrix dimension absorbs the fixed enlargement factor.

This is the exact input needed before
`sampled-weyl-defect-controls-common-pvm-dirichlet-energy`.  Ordinary dense
BLR supplies the algebraic conclusion but its complete pair table is not a
finite-template small-cancellation incidence object.  Equality-cloud degree
reduction recreates the known two-pair contour obstruction.

The mixed incidence **in isolation** is discharged for the private sampler.
`private-random-weyl-sampler-forces-growing-matrix-dimension` gives
the bounded-flexible matrix-valued dimension floor once the two additive actions
are exact; `private-matching-free-product-separates-pauli-signs` places every
mixed sign test as a constant-area conjugate with no mixed contour; and
`private-weyl-samplers-admit-recursive-selection` computes the finite label
lists.  The same-basis incidence can nevertheless join several private
basins into a combined contour.
`random-private-matching-eliminates-fixed-multibasin-contours` removes every
bounded such contour, while `sign-safe-unbounded-multibasin-placement`
records the residual asymptotic word-placement gate.  Thus the present node
is the sole analytic gate, not the sole finite-presentation gate.

The apparent shortcut through de la Salle Theorem 3.11 is circular here.
`de-la-salle-pauli-game-starts-after-the-same-pvm-gate` shows that the theorem
begins with one primitive full answer PVM, hence one exact additive action,
on each side.  Its uniform conclusion is valuable only after the present
same-PVM authentication has been achieved; it does not round the local LDPC
occurrences into that input PVM.

Spaas's chordal graph-product stability is also downstream rather than the
missing bridge.  `spaas-chordal-stability-does-not-cross-the-ldpc-quotient-gate`
records that the occurrence equalities and LDPC parity words are external
quotient relations, while collapsing them first destroys bounded occurrence.
Its strict stability theorem is for each fixed graph and supplies no modulus
uniform over the growing average-relator family.

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
