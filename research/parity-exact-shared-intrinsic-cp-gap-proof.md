---
rg: 2
id: parity-exact-shared-intrinsic-cp-gap-proof
kind: route
title: Collapse exact contraction faces to reflections and dominate the face Hamiltonian by coordinate pinchings
target: parity-exact-shared-contractions-have-intrinsic-cp-gap
requires:
  - repeated-ldpc-adjoint-face-hamiltonian-gap
  - tangent-commutator-covariance-bypasses-code-riesz-endpoint
  - intrinsic-finite-green-commutator-step-has-the-correct-tangent
---

The norm chain `(PES1)` proves that every contraction in an exact product
face is unitary; coverage of coordinates and selfadjointness give the first
assertion.

For a commuting reflection face, the maps `P_i` are commuting orthogonal
projections on `L_2(M)`.  Scalar comparison on their joint eigenspaces
proves `(PES3)`.  Average over faces.  Each coordinate quadratic form occurs
at most `deg(i)` times, so

```text
 <V,HV>
 <=(1/|faces|)sum_c sum_(i in c)<V,P_iV>
 <=C_occ<V,Pbar V>.                                    (PEP1)
```

Combine `(PEP1)` with the established face gap to obtain `(PES5)`.  Since
`Pbar` is a positive contraction with kernel exactly `K`, spectral calculus
gives `(PES6)` and the finite Green estimate.

For `(PES7)`, left and right multiplication by the reflection `Q'` give
sign `-1` on `pM(1-p)`, while `Ad(I)` is the identity.  This proves the
operator-norm discontinuity of equality transport despite vanishing
normalized-HS displacement.
