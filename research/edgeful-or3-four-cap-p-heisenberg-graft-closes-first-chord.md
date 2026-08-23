---
rg: 2
id: edgeful-or3-four-cap-p-heisenberg-graft-closes-first-chord
kind: route
title: Close the Fourier chord with a native odd-sector HS actuator
target: first-cycle-signed-hecke-chord
requires:
  - edgeful-or3-four-cap-walsh-packet
  - four-cap-common-phase-forces-trivial-mark
  - four-cap-two-chart-mixer-has-finite-clifford-evaluator
  - edgeful-or3-coefficient-link-compiler
  - affine-leavitt-p-heisenberg-hs-corner-blocker
  - overlap-subdivision-preserves-coherent-piece-obstruction
---

Use the Fourier coefficient-link compiler to close the cap-sector overlap
relations, and tensor its selected packet corner with the odd character
projection `(PHG5)`.  The exact graft preserves every packet atom and all
coefficient identities.  Its HS blocker removes every finite-matrix escape
which retains that selected corner, with no post-candidate dimension or
defect threshold.

The route remains conditional on two independent gates: the actual
cap-sector coefficient link, and the affine-Leavitt root-to-coefficient
decoder inherited by the odd-sector blocker.  The fixed Heisenberg transfer
itself is complete and loses only `(p-1)/2`.

There is no passive-graft shortcut between these gates.
`selected-odd-heisenberg-corner-is-native-matrix-amalgam` identifies the
whole selected coefficient corner as
`C[Gamma_A] *_(C[C_p]) M_p(C)`.  Amenable-edge permanence then shows that a
no-CE atlas in this corner already proves `Gamma_A` nonhyperlinear.  Thus
the coefficient link must genuinely use the native affine-Leavitt side; the
finite Heisenberg matrix packet only supplies the local context block and
the finite-dimensional-invisible selector.
