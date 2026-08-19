---
rg: 2
id: atlas-a4-packet-commutant-synchronization-proof
kind: route
title: Packet generation plus A8 averaging gives a multiplicity-independent commutant gap
target: atlas-a4-packet-commutant-synchronization
requires:
  - atlas-a4-packet-letters-generate-both-a8-charts
---

Fix one chart and write `lambda=lambda_k`.  By
`atlas-a4-packet-letters-generate-both-a8-charts`, the finite packet-letter set
`S` generates `A8`.  Choose once and for all, for every `g in A8`, a word
`w_g` in `S union S^{-1}`, and let `L` be the largest of these finitely many
word lengths.

For `||X||_op<=1`, commutator telescoping along `w_g` gives

```text
||[X,lambda(g)]||_2
 <= L sum_(s in S) ||[X,lambda(s)]||_2.
```

Using Cauchy--Schwarz on the fixed set `S`, absorb its cardinality into a
constant `C_0` and obtain

```text
max_(g in A8) ||[X,lambda(g)]||_2
 <= C_0 (sum_(s in S)||[X,lambda(s)]||_2^2)^(1/2).      (1)
```

Now average over the regular chart action:

```text
E(X)=(1/|A8|) sum_(g in A8) lambda(g) X lambda(g)^*.
```

This is the Hilbert--Schmidt orthogonal conditional expectation onto
`lambda(A8)'`.  Therefore

```text
dist_2(X,lambda(A8)') <= ||X-E(X)||_2
 <= (1/|A8|) sum_g ||X-lambda(g)Xlambda(g)^*||_2
 <= C_0 (sum_(s in S)||[X,lambda(s)]||_2^2)^(1/2)
```

by `(1)`.  The words `w_g`, hence the constant, live entirely in the fixed
finite group and do not depend on `k`.  The factor-two packet letters satisfy
the same exact generation statement, so the same argument applies on the
other chart.