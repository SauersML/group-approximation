---
rg: 2
id: root-normalizer-and-parahoric-counterexample-proof
kind: route
title: Preserve the root image-kernel flag and use the A2 parahoric section loop
target: root-type-loops-are-solvable-but-parahoric-loops-are-not
requires:
  - shortest-second-denominator-return-has-coweight-holonomy
  - first-root-parahoric-target-has-a-distinct-double-coset-type
  - native-a2-two-path-average-is-not-an-ordinary-word-compression
---

Any normalizer of `I+tE_12` normalizes the line spanned by `E_12` in the
matrix algebra.  It therefore preserves the image line and kernel plane of
`E_12`, hence belongs to the solvable Borel stabilizing that complete flag.
This proves the root-type half for arbitrary word length.

For the parahoric half, the already computed section identity has relative
word `d=x_23(2)`.  The Chevalley commutator
`[x_12(1),x_23(2)]=x_13(2)` shows directly that `d` does not normalize the
`12` root subgroup.  Since `d in D`, it is nevertheless a valid parahoric
endpoint holonomy.  The Fourier-support theorem for the two-path average
then supplies the precise reason this nonamenable-sector holonomy is not
automatically charged.

