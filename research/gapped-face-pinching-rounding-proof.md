---
rg: 2
id: gapped-face-pinching-rounding-proof
kind: route
title: Project to the common commutant, take central spectral signs, and classically decode
target: gapped-face-pinchings-give-same-hilbert-code-pvm-rounding
requires:
  - binary-face-pvm-is-determined-by-coordinate-reflections
---

Bound each whole-face pinching energy by the sum of its coordinate
commutator energies.  The assumed Hamiltonian gap controls distance to the
common commutant.  Conditional expectation sends every original coordinate,
which lies in the generated algebra, into the center of that commutant.
Round these central contractions by spectral sign and then apply the
classical LTC decoder atomwise to their joint PVM.  Every operation stays in
the original matrix algebra and the total squared HS movement is
`O(epsilon/gamma)`.
