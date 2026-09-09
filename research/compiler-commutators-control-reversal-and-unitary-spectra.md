---
rg: 2
id: compiler-commutators-control-reversal-and-unitary-spectra
kind: route
title: Rewrite the shared commutators and classify finite-unitary commutators of involutions
target: leavitt-compiled-p1-square-controls-matrix-reversal
requires:
  - leavitt-has-an-explicit-finite-c-killing-certificate
  - leavitt-eight-word-packet-is-quantitatively-equivalent
  - leavitt-seven-cell-thompson-completion-requires-moved-pairs
artifacts:
  - research/artifacts/leavitt-compiler-square-reversal-and-spectral-boundary-2026-09-08.md
---

The marked involutions give `x d x=y d y=d^-1` for
`d=[x,y]`, so the two centralization defects equal the `d^2`
defect. At the square anchor, writing `E=e`, `U=u`, and
`F=U E U^-1` makes `p_1^2=[E,F]`. The latter commutation is
not supplied merely by reversibility of `p_1`.

The other compiler word is exactly `q_1=(C^-1 B_3 C B_1)^2`
and is reversed by `B_1`. Replace `PQP` by its conjugate-word
counterpart `PQP^-1`; their distance is exactly `||P^2-I||`.
This gives the reversal bound and, by telescoping powers, the
imaginary-trace bounds without requiring the eight rows to vanish.

For the spectral characterization, conjugate eigenvalue pairs are
realized by explicit two-dimensional involutions. The `-1` block
must have even dimension, as also follows from determinant one.
The remaining `+1` block can balance both involution traces when
the total dimension is even. The source word already has determinant
one, so this parity provides no independent obstruction once the
spectral symmetry holds.

The construction classifies freely chosen matrix involutions only.
It does not reconstruct their shared source occurrences, import
eventual-tail classes into matrices, or decide whether `p_1^2`
is an abstract consequence of `T_8`.
