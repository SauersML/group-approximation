---
rg: 2
id: binary-leavitt-purely-infinite-by-monomials-proof
kind: route
title: Push right by a long word, invert a longest word, and shift past the tails
target: binary-leavitt-algebra-is-purely-infinite-by-monomials
requires: []
artifacts:
  - research/artifacts/leavitt-inverse-defect-normal-forms-2026-09-12.md
---

## Why sufficient

Complete direct proof, Section 1 of the artifact (with (M1)-(M3) of Section 0).
Let `m` be the longest ghost word in an expression of `x`. The identity
`x = sum_(|gamma|=m) x S[gamma] T[gamma]` gives some `y = x S[gamma] != 0`,
which is a sum of words `S[alpha]`. For a longest `alpha*`,
`T[alpha*] y = 1 + sum_(delta in D) T[delta]` with nonempty `delta` of
distinct lengths. With `w = 0 1^L` and `L >= max |delta|`, each `T[delta] S[w]`
is `0` or `S[1^j]` with `j >= 1`, and `T[w] S[1^j] = 0` because `1^j` is not a
prefix of `w`. Hence `T[w] T[alpha*] y S[w] = 1`.
