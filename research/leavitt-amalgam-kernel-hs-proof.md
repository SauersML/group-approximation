---
rg: 2
id: leavitt-amalgam-kernel-hs-proof
kind: route
title: A killed reduced word changes canonical trace by one and costs square-root-two in HS
target: leavitt-amalgam-microstates-have-unrepairable-kernel
requires:
  - leavitt-one-compressor-join-is-proper-amalgam-quotient
  - leavitt-first-mixed-amenable-face-relator
---

Choose `1 != k in ker q`, which exists by the first required claim. The
canonical group trace of `G` has `tau_G(k)=0`. Therefore any canonical
hyperlinear (indeed sofic permutation) microstate sequence obeys

```text
||sigma_n(k)-1||_2^2
 = 2-2 Re tr(sigma_n(k)) -> 2.
```

Fix a word for `k` of length `m` in a finite generating set. If each generator
matrix is changed by at most `epsilon_n` in normalized HS, repeated use of
unitary invariance and the triangle inequality changes the evaluated word by
at most `m epsilon_n`. Thus `epsilon_n->0` leaves its distance from the
identity converging to `sqrt(2)`, rather than zero.

For the explicit base word `r`, the same calculation applies with amalgam
syllable length four. Its image in the literal Leavitt group is exactly one,
so the trace changes from zero in the reduced amalgam to one in the quotient.
This unit trace jump is the complete perturbative obstruction.
