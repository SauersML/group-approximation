---
rg: 2
id: binary-cylinder-words-have-a-256-quadratic-bound
kind: claim
title: Short decoder certificates and unpadded recursion improve binary cylinder witnesses to 256 times the squared block length
distinct_from:
  binary-subshift-language-has-quadratic-group-witnesses: that gives a 2^17 quadratic bound; this replaces the constant words and removes padding to give a 2^8 bound, with explicit short coefficient certificates.
artifacts:
  - research/artifacts/pestov91-short-involution-mf-implications-2026-09-13.md
  - research/artifacts/find-pestov91-short-decoder-2026-09-13.py
---

For every nonempty binary word `A` of length `n`, a uniform polynomial
construction gives a word `W_A(c,t,w)` evaluating to its cylinder root
`e_12(1_[A])` in every binary subshift elementary group. Its length is
at most `167n^2-100n-49<256n^2`. Thus it is the identity exactly when
`A` is absent. Five constant words of lengths at most eighteen give
the required coefficient roots, swaps and a transport word of length
44; the recurrence works at unequal child lengths without padding.
