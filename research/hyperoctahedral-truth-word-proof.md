---
rg: 2
id: hyperoctahedral-truth-word-proof
kind: route
title: Separate all coordinates in the direct power of the alternating group
target: hyperoctahedral-balanced-word-truth-table
requires: []
---

Inside `S_N^A`, the diagonal `A_N` and its conjugate by the tuple of regular
translations form a subdirect product.  The diagonal-block classification for
powers of the nonabelian simple group `A_N` says two coordinates could share a
block only if their translations differed by an element centralizing `A_N`;
that centralizer is trivial.  Hence all alternating coordinates are independent.
Conjugating diagonal even-sign flips by these coordinatewise alternating
elements supplies independent even-sign coordinates, so the generated group
is `(B_N')^A`.  The scalar `-I` lies in `B_N'`; choose it precisely on the
desired assignment set.  Replacing the two diagonal generators by constants
and router conjugates yields a word of router exponent sum zero, proving both
the truth table and multiplicity cancellation.
