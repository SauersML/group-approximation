---
rg: 2
id: km-reduced-harris-has-no-fd-boundary-representations
kind: claim
title: The Kac-Moody reduced Harris range has no finite-dimensional boundary-representation hull
distinct_from:
  km-harris-maximal-matrix-range-collapse: that remains a viable UCP matrix-range target; this rules out proving it from finite-dimensional star representations or finite quotients.
  caprace-thom-v2-leaves-km-character-rigidity-open: that corrects a character-rigidity citation; this uses only finite generation, infinitude, simplicity, property T, and the reduced norm.
---

**ESTABLISHED FENCE.**  For the explicit group `Gamma` in
`simple-kazhdan-kac-moody-lattices-exist`, the reduced algebra
`C*_r(Gamma)` has no unital finite-dimensional star representation.
Consequently the Harris system in matrices over that algebra has no
finite-dimensional boundary representation, and no finite-quotient or
finite-dimensional-representation hull can prove `(KMH1)`.

Indeed, a finite-dimensional star representation of `C*_r(Gamma)` restricts
to a finite-dimensional unitary representation of `Gamma`.  Simplicity
makes a nontrivial such representation faithful.  But a finitely generated
linear group is residually finite, whereas an infinite simple group has no
nontrivial finite quotient.  Hence the restricted representation must be
trivial.  The trivial representation factors through `C*_r(Gamma)` exactly
when `Gamma` is amenable; this `Gamma` is infinite with property T and is
therefore nonamenable.  No representation remains.

The same conclusion holds after Harris's fixed matrix amplification.  Since
the system is hyperrigid and its C-star envelope is the full amplified
reduced algebra, every boundary representation extends to a star
representation of that envelope, so none is finite dimensional.

This does not refute the matrix-range route.  Every level `W_k(T_Gamma)`
still contains UCP images, for example the canonical trace followed by a
scalar amplification.  It proves that the necessary finite-level data must
come from genuine compressions of infinite-dimensional representations,
not from finite quotients, finite-dimensional characters, or an RFD
approximation of the C-star envelope.  Free-spectrahedral approximation in
`(KMH2)` remains logically available because its defining matrices encode
UCP matrix-order data rather than representations of `C*_r(Gamma)`.
