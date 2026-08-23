---
rg: 2
id: common-source-cell-closes-s3-endpoints
kind: route
title: Specialize the capacity-gated common-source cell to the three S3 endpoint contexts
target: s3-equivariant-endpoint-conventions-use-global-bcs-words
requires:
  - regular-induced-affine-reset-synchronizes-s3-holonomy
  - regular-clifford-edge-map-has-zero-kernel
  - gauge-doubling-gives-selector-flip-symmetries
  - capacity-gated-s3-endpoint-common-source-cell
  - common-source-covariance-locks-binary-marginals
  - labelled-pvm-branch-gram-gives-lin-corner
  - one-s3-row-rounds-joint-source-pvm
  - positive-cross-gram-state-rounds-to-common-pvm
---

Use the private regular edge to synchronize the three reset transports while
retaining the original logical BCS words.  There are two valid downstream
interfaces, and they must not be conflated.

If the original two covariance rows `(SEC2)` are retained,
`one-s3-row-rounds-joint-source-pvm` constructs the exact four-atom source PVM
with explicit linear loss.  Once that PVM and the corresponding role-amplified
target labels live on the same reservoir, apply `(SEC6)--(SEC8)`.  The block
Gram `G=sum_iF_iT_iE_i` then carries every encoded label exactly, and the
scalar mass floor `(SEC8)` is the only remaining *downstream* input.  It does
not erase the upstream obligation to make `(SEC2)` pay relator energy.

Without a joint source PVM for `Z_X,Z_Y`, use the hypothesis-minimal endpoint
`(SEC9)--(SEC12)`.  Anchor one binary endpoint exactly in `G_X`; keep the other
endpoint, the transitive `S3` role, and the return word as mixed covariance rows
on this **same** `G_X`.  The certificate `(SEC12)` supplies both its fixed mass
and all of those rows.  `positive-cross-gram-state-rounds-to-common-pvm` then
extracts the fixed-density common packet corner.  A mass estimate alone does
not close this one-bit variant.

On the resulting single Gram state, `(CSM2)--(CSM3)` identify the `X` marginals
of `00,01` and the `Y` marginals of `01,11` with total error
`O(sqrt(E_rel))`.  The target residuals `(SEC3)` are the two diagonal and one
crossed failure projections, so `(CSM4)` bounds convention failure by the same
energy.  The source-commutator rows are not an additional hypothesis:
`labelled-pvm-branch-gram-gives-lin-corner` derives them from common-Gram
covariance by `(SEC5)`.

Gauge doubling fixes `Z_X,Z_Y` and the native mark while all private shares
and residual factors remain private, as required by the zero-kernel audit.
On the exact HALT witness the forbidden source `Q` vanishes, so every
capacity-gated row is zero and the attachment extends after the already
allowed countable amplification.  Thus either the complete-label certificate
`(SEC8)` or the honest one-bit certificate `(SEC12)` supplies precisely the
finite-matrix and exact-completeness clauses of the target endpoint claim.
