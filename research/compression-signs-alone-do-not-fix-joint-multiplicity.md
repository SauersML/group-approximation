---
rg: 2
id: compression-signs-alone-do-not-fix-joint-multiplicity
kind: claim
title: Compression signs alone do not determine joint character multiplicities
distinct_from:
  sampled-coordinate-joint-pvm-tracks-terminal-character-hash: that may also use vanishing contraction-to-sign error and low-energy cut provenance; this refutes the tempting sign-only Hall argument
  common-character-rotation-is-flat-for-involution-jacobian: that preserves the same two character multiplicities under a rotation; this changes the apparent compressed character menu completely
---

There are four commuting reflections with joint spectrum supported on four
binary characters, and a rank-one PVM with four atoms, such that the signs
of all compressed reflections on those atoms are four **disjoint** binary
characters.

Concretely, index the standard basis by the even-parity words in `F_2^3`
and let `Q_k` be the diagonal sign of bit `k`.  There is a real conference
matrix `C` of order four, with zero diagonal, all off-diagonal entries in
`{+1,-1}`, and

```text
C C^T=3I.
```

Index its rows by odd-parity words so that the zero entry excludes the
unique even word at Hamming distance three.  The other three supported even
words are the Hamming-distance-one neighbors.  The normalized rows of
`C/sqrt(3)` form an orthonormal basis; let `(f_t)` be their rank-one PVM.
Then, for every odd word `t` and coordinate `k`,

```text
f_t Q_k f_t=(1/3)(-1)^(t_k) f_t.                        (CSM1)
```

Thus the compressed signs are exactly the four odd characters, although
the true joint spectrum contains only the four even characters.  No
label-preserving unitary matching exists because simultaneous conjugacy
preserves joint spectral multiplicities.

Repeating each of the three coordinates gives a positive-distance binary
code with bounded equality checks, so the phenomenon is compatible with an
exact bounded parity layer.  It is excluded only when the diagonal
contraction-to-sign error tends to zero: here that error is the fixed value
`(1-1/3)^2` on every coordinate and atom.

## Attempts

An abstract Hall theorem based only on the signs of `fQ_kf` is therefore
false, even when the raw reflections commute exactly.  The surviving
quantity is the **margin** `||fQ_kf-sign(fQ_kf)||_2`, not the sign itself.
