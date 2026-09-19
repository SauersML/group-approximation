---
rg: 2
id: primitive-shell-bs-clock-has-optimal-opnorm-matcher-proof
kind: route
title: Match all cycle roots to the sorted primitive roots
target: primitive-shell-bs-clock-has-optimal-opnorm-matcher
requires: []
---

Multiplication by `2^(-1)` is transitive on the units modulo `3^n`, because
`2` has order `phi(3^n)=L`.  Hence `P` is one cycle of length `L` on `H_n`,
and its spectrum consists of all `L`-th roots of unity, each once.  The
spectrum of `D` consists of the primitive `q`-th roots, also each once.

List the latter in increasing argument.  If `0<=k<L`, the `k`-th positive
integer not divisible by `3` is

```text
u_k=floor(3k/2)+1.                                   (1)
```

Since `L=2q/3`,

```text
0 < u_k/q-k/L <=1/q.                                 (2)
```

Choose an eigenbasis `(v_k)` of `P` whose eigenvalues are the `L`-th roots
in increasing argument, and define `K_n v_k=e_(u_k)`.  Then `K_n` is unitary,
both `D` and `K_n P K_n^*` are diagonal in the standard unit-shell basis,
and `(2)` gives

```text
||D-K_n P K_n^*||
 <=max_k 2 pi |u_k/q-k/L|
 <=2 pi/q.                                           (3)
```

For the converse, `1` belongs to the spectrum of every conjugate of `P`,
whereas the closest primitive `q`-th roots to `1` are
`exp(+2 pi i/q)` and `exp(-2 pi i/q)`.  Spectral variation for normal
matrices therefore gives

```text
||D-K P K^*||
 >=dist(1,spectrum(D))
 =2 sin(pi/q)                                        (4)
```

for every unitary `K`.  This proves `(PSM2)`.

The even cycle length `L` puts `-1` in the spectrum of `P`, proving the
first part of `(PSM3)`.  Finally `D` has simple spectrum, so its commutant is
diagonal.  A diagonal matrix commuting with the transitive permutation `P`
is constant on the one unit orbit, hence scalar.  This proves the second
part and finishes the claim.
