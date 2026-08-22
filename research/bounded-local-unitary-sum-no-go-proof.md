---
rg: 2
id: bounded-local-unitary-sum-no-go-proof
kind: route
title: Reuse a proof across two close scalar phase boundaries and telescope every local word
target: bounded-local-group-relators-cannot-test-continuous-normalized-unitary-sum
requires:
  - rooted-normalized-sum-linear-pcpp-needs-sqrt-n-norm
---

Use the exact scalar-unitary good and bad phase vectors `(RNS7)--(RNS9)`.
Completeness supplies auxiliaries for the good vector; keep them fixed after
changing only the leaves.  For each word, replace its boundary letters one
occurrence at a time.  Left and right multiplication by unitaries preserve
normalized Hilbert--Schmidt norm, and inversion preserves the distance
between two unitaries, so the word distance is at most the sum of the changed
letter distances.  Cauchy--Schwarz with at most `q` boundary occurrences gives
`(BLU5)`.  Reverse the finite sums and use the weighted occurrence inequality
`(BLU2)` to obtain `(BLU6)`.  Since the normalized sums of the two phase
vectors are one and zero, respectively, `(BLU6)` contradicts every fixed
positive soundness gap.

