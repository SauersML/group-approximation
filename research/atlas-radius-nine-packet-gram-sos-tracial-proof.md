---
rg: 2
id: atlas-radius-nine-packet-gram-sos-tracial-proof
kind: route
title: Interpret every fixed packet Gram operation in the regular finite von Neumann algebra
target: atlas-radius-nine-packet-gram-sos-is-tracial
requires:
  - global-tracial-positivity-cannot-separate-group-trace
---

Let `(M,tau)` be any finite tracial von Neumann algebra and let the fixed
packet group `H` act by the prescribed unitaries.  Formula `(PGS1)` is a
unital completely positive trace-preserving conditional expectation: it is a
finite average of inner `*`-automorphisms.

Complete positivity gives `(PGS2)>=0`.  Explicitly, for any column
`b=(b_i)` over `M`,

```text
b^*[E_H(a_i^*a_j)]b
 =E_H((sum_i a_i b_i)^*(sum_j a_j b_j))>=0
```

when the coefficients are placed in the fixed-point algebra; in full
generality `(PGS2)` is the standard complete-positivity matrix of `E_H` and is
positive in `M_k(M)`.  Fixed matrix amplification, principal compression,
positive linear combination, and the normalized trace all preserve
positivity.

If a positive block matrix has a strictly positive lower-right pivot `C`, its
Schur complement `A-BC^(-1)B^*` is positive.  This is a C*-algebra identity,
obtained by conjugating the block matrix by

```text
[[I,-BC^(-1)],[0,I]],
```

and remains valid in `M_k(M)`.  Replacing `C` by `C+epsilon I` covers every
fixed regularized use.  Sums of Hermitian squares and squared relator
residuals are positive in `M` as well.

Thus every step of the proposed packet-Gram calculus is sound in arbitrary
finite tracial von Neumann algebras, with exactly the same constants and
finite packet averages as in matrices.  Apply the calculus in
`M=L(Gamma)` to the left regular atlas generators.  The relator residuals
vanish, so `(PGS3)` would imply `tau_Gamma(P)>=0`, contradicting its required
negative value.  The required established firewall supplies precisely this
last semantic implication.

Isotypic diagonalization does not change the conclusion: it is a fixed
finite-dimensional Fourier transform in `M_k(M)`.  Hence neither the A4
symmetry nor its conditional-expectation gap introduces matrix-only data.
