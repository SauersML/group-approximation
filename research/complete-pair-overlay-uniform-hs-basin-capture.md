---
rg: 2
id: complete-pair-overlay-uniform-hs-basin-capture
kind: claim
title: Capture small-defect balanced-overlay tuples in a uniform mixed-norm Newton basin
distinct_from:
  repeated-ldpc-shared-face-marginal-synchronization: that asks for the final same-Hilbert exact correction; this asks only for entry into a fixed operator-norm tube where the established Jacobian gap performs the correction
  quadratic-overlay-has-uniform-linearized-synchronization-gap: that proves uniform transversality at every exact point; this is the global compactness or truncation step needed to reach such a point
  normalized-hs-taylor-remainder-is-not-dimension-free: that gives the generic sparse high-operator-norm obstruction; this asks for the parity and complete-pair relations to pay for and remove precisely that sparse sector
  covariant-square-function-has-common-reducing-threshold: that turns an already covariant positive error operator into one common reducing outlier cut; this must construct such an operator from the balanced occurrence residuals and then correct the diffuse complement
---

OPEN.  Prove a dimension-independent basin-capture theorem for the **balanced**
repeated LDPC occurrence presentation with equality expanders, bounded parity
faces, and the complete logical-pair overlay.  If there are `M` original
parity faces and `Theta(M^2)` quadratic overlay faces, every original face
must also be repeated `Theta(M)` times.  Otherwise the all-equal nonzero
syndrome coset has only `O(1/M)` normalized defect while remaining a constant
distance from the code.

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

`covariant-square-function-has-common-reducing-threshold` supplies the latter
cut from a positive error operator `H` once both `tau(H)=o(1)` and average
covariance `avg_i ||[H,Q_i]||_2=o(1)` are known.  The unresolved concrete
subproblem is therefore to build a **balanced-overlay covariant defect square
function**.  The raw sum of relator squares has small trace, but conjugating
it by one coordinate does not literally permute the relator family; proving
small covariance without expanding words through a length-dependent Dehn
argument is exactly where the parity and complete-pair symmetry must enter.
