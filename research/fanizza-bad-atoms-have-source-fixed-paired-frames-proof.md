---
rg: 2
id: fanizza-bad-atoms-have-source-fixed-paired-frames-proof
kind: route
title: Atom-normalize the Schur gate and audit the coordinate-pivot obstruction
target: fanizza-bad-atoms-have-source-fixed-paired-frames
requires:
  - fanizza-fixed-nonlinear-menu-has-small-rank-gates
  - every-forbidden-atom-has-fixed-schur-pauli-words
  - two-center-paired-frames-cannot-isolate-the-joint-hot-bit
artifacts:
  - experiments/fanizza_atom_paired_frame_search.py
---

For a bad atom `a`, the row and column operations in the proof of `(SPW4)`
give `diag(U(a),1)`.  A further row operation by `U(a)^-1` changes this to the
identity without moving the last row or column.  Hence the last coordinate is
still the literal Schur pair, and every leading coordinate is a possible
baseline core pair.

For each core choice, restrict the transformed symbolic matrix to the core and
last rows and columns.  Form the four-generator plus and minus frames using
`(SFF1)`.  The script checks both

```text
ker(Phi_plus)=ker(Phi_minus)
```

for the combined frame and the stronger equality for the coefficient
commutator maps alone.  The latter makes the induced center isomorphism fix all
source selectors.  It then evaluates every coefficient character, checks
minus rank zero at `(a,a)`, plus rank two, and searches the minus characters
for a rank-two target with source component `a`.

Every one of the `2+4+20=26` atoms has a source-fixed witness.  However, all
witnesses have the same coefficient kernel of size four, hence kernel
dimension two and commutator-image rank four.  The canonical support/E5 frame
has coefficient-kernel size eight, hence kernel dimension three and image
rank three.  The script additionally exhausts all `20160` elements of
`GL_4(F_2)` and finds no word change carrying the support kernel to the
Fanizza kernel; the differing kernel dimensions already force this result.

Consequently the search proves source-atom preservation but also proves that
the coordinate-core construction is a full-center chart.  It cannot be used
as the rank-three E5 interface.  All matrix evaluations, kernel codes,
inverses, and ranks are over `F_2`; there is no numerical tolerance or
randomized step.
