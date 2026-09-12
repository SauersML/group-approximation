---
rg: 2
id: complex-gap-binary-filling-fence-proof
kind: route
title: Compare mod-two coset leaders with real pseudoinverse fillings
target: complex-hecke-gap-does-not-bound-binary-syndrome
requires:
  - diagonal-parity-is-hecke-but-tau-misses-local-links
  - binary-cubic-curl-has-global-torus-hecke-blocks
---

If \(c'\in\ker\overline D\), then
\(e=c-c'\) satisfies \(\overline De=\overline Dc\), and its support is
the Hamming disagreement set of \(c,c'\). Conversely, every filling
\(e\) of \(\overline Dc\) makes \(c-e\) a codeword. Taking minima proves
(CGF2).

The singular-value estimate (CGF3) is the defining norm estimate for the
Moore--Penrose inverse on \(\operatorname{ran}D_{\mathbb C}\). It is a
statement about complex vectors and Euclidean norm. For a binary vector,
each coordinate of \(D\widetilde c\) has the same parity as the
corresponding coordinate of \(\widetilde h\), so their difference is
coordinatewise even. This proves the unique decomposition (CGF4).

In (CGF5),
\[
 D_0\widetilde c_0=1+1=2
\]
while its reduction is zero because \(2=0\) in \(\mathbb F_2\).
The rank-one matrix has sole nonzero singular value equal to the Euclidean
norm of its row, namely \(\sqrt3\). Singular values of a block diagonal
direct sum are the union of the singular values of its blocks, proving
the stable family assertion.

Finally, the diagonal parity theorem identifies the modular cubic
syndrome with the reduction of the displayed integral matrix \(D\), and
the Hecke theorem computes the characteristic-zero normal \(D^*D\).
Equation (CGF2) says that the desired Hamming modulus is exactly (CGF7).
Since the even vector \(2q\) in (CGF4) is unconstrained by syndrome
support, applying a complex pseudoinverse to \(D\widetilde c\) does not
bound (CGF1). An additional integral or mod-two filling theorem is
logically necessary.
