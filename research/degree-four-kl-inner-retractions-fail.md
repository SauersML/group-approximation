---
rg: 2
id: degree-four-kl-inner-retractions-fail
kind: claim
title: No cycle or coordinate-packet inner retraction fences the degree-four KL gadget
artifacts:
  - research/degree-four-kl-inner-retractions-fail-proof.md
  - research/artifacts/screen-degree4-full-copy-inner.py
distinct_from:
  degree-four-kl-source-face-retraction: that builds a countermodel for an abstract packet presentation; this tests homomorphisms of four entire Leavitt coefficient copies and finds no retraction in the first canonical family.
  kl-violating-equation-over-leavitt-unit-group: that requires proof that a coefficient copy dies; failure of a finite retraction family is not such a proof.
---

For the degree-four candidate with slots `(r,e,a,c,1,b,d,p)`, fix the
zeroth coefficient copy.  Map each of the other three full copies either
trivially, by one of the twenty cycle-inner automorphisms `Ad(p^k)`, or by
`Ad(p^k q p^(-k))` for one of the twenty coordinate conjugates of the mixed
packet `q`.  Let the first Schreier relator determine `z` uniquely.

None of the `41^3=68921` resulting maps satisfies the remaining relators.  In
fact the second cyclic lift `R1` already fails in every case.  Each rejection
is certified by a concrete moved basis vector in the faithful infinite-word
Leavitt module; no finite quotient or word-length truncation is used.

This closes only the trivial/cycle/one-packet-inner retraction family.  General
self-similar embeddings, non-inner automorphisms, and arbitrary graph-of-groups
targets remain open, so the result is neither coefficient injectivity nor a KL
violation.
