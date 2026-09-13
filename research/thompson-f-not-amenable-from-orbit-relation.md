---
rg: 2
id: thompson-f-not-amenable-from-orbit-relation
kind: route
title: A non-amenable measured orbit relation of F on the interval would make Thompson's F non-amenable
target: thompson-f-is-not-amenable
requires:
  - thompson-f-interval-orbit-relation-is-nonamenable
---

A non-singular action of an amenable countable group is amenable in Zimmer's sense, and its
orbit equivalence relation is amenable (Zimmer, Invent. Math. 41 (1977)). So if some
`F`-quasi-invariant measure on `(0,1)` makes the orbit relation of `F` non-amenable, `F` is
non-amenable. This is the one-way test behind Monod's theorem for `H(A)` (arXiv:1209.5229,
Theorem 1.1).

This route never fires: its premise is refuted by
`thompson-f-interval-orbit-relation-is-hyperfinite`. It is recorded so that the certificate
class is visibly dead, without a `requires: []` dead route into this famous root.
