---
rg: 2
id: complete-overlay-code-group-has-uniform-conjugation-gap
kind: claim
title: The exact complete-overlay code group has conjugation gap four times the code distance
distinct_from:
  uniform-kazhdan-homogeneous-lcs-face-groups: that seeks a useful gap before complete-overlay exactification; this computes the easy gap after every logical pair already commutes.
  quadratic-repetition-supports-complete-commutation-overlay: that realizes the all-pairs relations with bounded occurrence; this computes the representation-theoretic gap of the resulting abstract group.
---

Let `C<=F_2^L` be a binary linear code of relative distance `delta`, presented
by homogeneous parity checks.  Add every logical pair commutator to the
homogeneous face group.  The resulting abstract group is the finite abelian
code-dual group

```text
G_C=<x_1,...,x_L | x_i^2=1, [x_i,x_j]=1, parity checks>.
```

For every finite-dimensional unitary representation `pi` and every matrix
`V`,

```text
(1/L)sum_i ||Ad(pi(x_i))V-V||_2^2
 >= 4 delta dist(V,pi(G_C)')^2.                            (COC1)
```

Indeed, decompose the representation into character spaces.  Characters of
`G_C` are codewords in `C`.  On the matrix block from character `chi` to
character `psi`, conjugation by `x_i` has sign `(-1)^(chi_i+psi_i)`.  If
`chi!=psi`, their difference is a nonzero codeword and has weight at least
`delta L`; the average displacement on that block is therefore at least
`4 delta`.  Equal-character blocks are exactly the commutant.  Orthogonality
of the matrix blocks proves `(COC1)`.

By `quadratic-repetition-supports-complete-commutation-overlay`, all logical
pair relations admit a bounded-occurrence presentation using `Theta(L^2)`
copies.  Thus a positive-rate base code does yield an explicit homogeneous
LCS family with a uniform normalized conjugation gap and bounded-width,
bounded-occurrence expanded presentation.

This does **not** close approximate same-PVM rounding.  To invoke `(COC1)`,
the repeated pair contexts must first be exactified to one representation of
`G_C`; but exact copy equality plus those pair contexts already makes all
logical coordinates commute and glues the global code PVM.  Using the easy
abelian gap to perform that exactification would be circular.  The useful
open target is a parity-face gap before complete-overlay exactification.
