---
rg: 2
id: full-signed-whitehead-amalgam-fd-collapse-proof
kind: route
title: Propagate the active kernel ideal through all three Whitehead occurrences and collapse the controlled packet
target: full-signed-whitehead-amalgam-has-fd-invisible-clifford-mark
requires:
  - affine-leavitt-steinberg-mark-is-fd-invisible
  - odd-leavitt-prefix-whitehead-transport
  - controlled-pauli-corner-has-clifford-groupification
  - separate-balanced-hnn-cross-gram-is-typed-overlap
---

The prefix cancellation table gives `(FWA2)`, and direct multiplication
gives `(FWA3)`.  Quotienting the Steinberg group by the one relator `W^4`
does not kill either `W` or the active root because the elementary-matrix
image has `W` of order four and has nonzero active root.  The explicit local
monomial model supplies the other faithful `C_4` edge, so normal form for a
free product with finite cyclic amalgamation proves `J!=1`.

For an exact finite-dimensional representation, use the finite-root-kernel
ideal from the affine-Leavitt exact collapse theorem.  Active support puts
all four coefficients `e,f,x,y` in that ideal, so the three evaluated root
factors of `W` are the identity.  The amalgam identifies `u` with `W`, hence
`u=1`.  The local odd row gives `t=Z_1`.  Comparing this with the two
controlled-Pauli covariance rows first gives `Z_1=1`, then `Z_2=1`, and the
Pauli commutator gives `J=1`.

No approximate-kernel intersection is used or asserted.
