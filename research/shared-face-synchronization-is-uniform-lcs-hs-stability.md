---
rg: 2
id: shared-face-synchronization-is-uniform-lcs-hs-stability
kind: claim
title: Shared-face synchronization is uniform HS stability of the homogeneous LCS colimit
distinct_from:
  spaas-chordal-stability-does-not-cross-the-ldpc-quotient-gate: that checks one graph-product theorem against the LDPC quotient; this identifies the synchronization claim itself with the uniform quotient-stability problem.
  constant-size-private-basins-give-uniform-root-control: that transfers already corrected anchors to selected roots; this concerns simultaneous exactification of every face and every shared marginal.
  binary-face-pvm-is-determined-by-coordinate-reflections: that reconstructs atoms from commuting shared reflections; this explains why averaging first does not provide those commuting reflections.
---

Let `G_H` be the homogeneous binary LCS/face group with one involution `x_i`
per logical coordinate, local commutators inside every check, and the local
parity words.  Let `P_H^occ` be its repeated occurrence presentation: one
copy `x_(i,c)` in each face/layer plus equality-expander relators joining the
copies of each `i`.

Exact representations of `P_H^occ` are exactly representations of `G_H`:
the equality relators collapse all copies, and
`binary-face-pvm-is-determined-by-coordinate-reflections` reconstructs every
face PVM.  Consequently
`repeated-ldpc-shared-face-marginal-synchronization` is precisely a uniform,
same-matrix-dimension HS-stability theorem for the growing family `(G_H)`
measured in the redundant bounded-occurrence presentations `P_H^occ`.

Equality expansion proves a Hilbert-space Poincare estimate for the bare
occurrence reflections.  It does not prove this quotient stability.  If one
averages the copies of each coordinate and rounds the average spectrally,
the resulting shared reflections need not commute within a face.  The atom
formula

```text
P_a=prod_i (I+(-1)^(a_i)Q_i)/2
```

is a PVM only after that commutation has been established.  Correcting each
face again can move its marginals away from the synchronized reflections.
Thus the proposed expander-plus-Lipschitz proof is circular at exactly the
simultaneous face/overlap correction step.

This is a reduction, not a refutation: special LCS colimits may possess the
required uniform stability.  But neither constant-degree equality expansion
nor bounded face width closes it without a new quotient/amalgam stability or
operator agreement theorem.
