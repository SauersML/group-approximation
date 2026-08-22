---
rg: 2
id: complete-pair-overlay-uniform-hs-basin-capture
kind: claim
title: Capture small-defect complete-overlay tuples in a uniform mixed-norm Newton basin
distinct_from:
  repeated-ldpc-shared-face-marginal-synchronization: that asks for the final same-Hilbert exact correction; this asks only for entry into a fixed operator-norm tube where the established Jacobian gap performs the correction
  quadratic-overlay-has-uniform-linearized-synchronization-gap: that proves uniform transversality at every exact point; this is the global compactness or truncation step needed to reach such a point
  normalized-hs-taylor-remainder-is-not-dimension-free: that gives the generic sparse high-operator-norm obstruction; this asks for the parity and complete-pair relations to pay for and remove precisely that sparse sector
---

OPEN.  Prove a dimension-independent basin-capture theorem for the repeated
LDPC occurrence presentation with equality expanders, bounded parity faces,
and the complete logical-pair overlay.

One sufficient formulation is the following.  There are fixed `r>0` and a
modulus `eta(epsilon)->0` such that every tuple of occurrence reflections
with average squared relator defect at most `epsilon` can be changed by
average squared normalized-HS cost at most `eta(epsilon)` so that it lies in
the operator-norm `r`-tube, modulo simultaneous unitary conjugacy and
character multiplicities, of the exact representation variety.  The radius
must be smaller than the mixed-norm Newton radius in `(QLS5)`.

Together with
`quadratic-overlay-has-uniform-linearized-synchronization-gap`, this implies
`repeated-ldpc-shared-face-marginal-synchronization`: the uniform Jacobian
inverse and the fixed-word mixed-norm Taylor estimate run Newton inside the
tube, while the discarded sector has already been paid in normalized HS.

## Attempts

Bare normalized-HS Newton does not prove basin capture.  A perturbation
supported on a projection of trace `alpha` can have operator norm one and
`2`-norm `sqrt(alpha)`; products of two copies can still have `2`-norm
`sqrt(alpha)`, rather than `alpha`.  Thus the quadratic Taylor remainder is
only linear at exactly the sparse scales that must be truncated.  The
complete-pair Jacobian gap rules out diffuse infinitesimal soft modes but
does not bound the trace of this high-operator-norm sector.  A successful
attack must use parity/complete-pair testing nonlinearly to charge that
sector, or construct a common approximately reducing cut before applying
the local theorem.
