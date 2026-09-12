---
rg: 2
id: leavitt-kl-violation-from-distinct-same-sign-labels
kind: route
title: Dead - look for a Leavitt violation among words with four distinct same-sign labels
target: kl-violating-equation-over-leavitt-unit-group
requires: []
---

**Dead.** Invalidated by `kl-four-same-sign-corner-words-inject`.

Split the powers of `t` into single letters. Suppose a nonsingular word has:
- at least four same-sign corners;
- pairwise distinct P-labels and pairwise distinct N-labels;
- no P-label inverse to an N-label.

Then it is aspherical over every coefficient group, so it injects `R^x` and
cannot violate.

This covers the length-six classes `+++++-` and `++++--` with no
finite-order hypothesis on the sign-change coefficients. It includes the
full-support torsion candidate `(L6.1)`.

A surviving candidate with four or more same-sign corners must repeat a
same-sign label, for instance with two same-sign squares `t^2`, or pair a
P-label with the inverse of an N-label. Recorded so that the census does not
revisit these words.
