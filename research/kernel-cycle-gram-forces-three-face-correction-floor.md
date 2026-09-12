---
rg: 2
id: kernel-cycle-gram-forces-three-face-correction-floor
kind: route
title: Read the kernel cycle as a positive face Gram matrix and apply the ambient Stinespring gap
target: three-face-ucp-balancing-needs-macroscopic-tree-motion
requires:
  - kernel-relator-forces-two-edge-ucp-section-gap
  - triangle-colimit-llp-reduces-to-relator-local-splitting
---

Restrict a ucp map on the three-face Fourier operator system to its full
`C^*(P_13)` summand.  The proof of the kernel-relator gap is ambient: it needs
only Stinespring positivity, the identity `v_1...v_L=1`, and the infinite-order
unitary `u_n` in the faithfully embedded edge amalgam.  It therefore gives
`(TFB2)` with the same constant even when the map takes values in all of
`C^*(G_0)` and is not a section.  Writing the prefix products of the `v_j`
produces the explicit positive Gram matrix `(TFB4)`.  Because each `v_j` is
simultaneously a closing-face element and an element of one tree face, the
forced displacement is a tree-face correction.  Taking distance from a
canonical linear lift gives `(TFB5)`.
