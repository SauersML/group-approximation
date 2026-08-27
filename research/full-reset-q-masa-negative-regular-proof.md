---
rg: 2
id: full-reset-q-masa-negative-regular-proof
kind: route
title: Restrict the unique reset ray sector by sector to the full q-MASA
target: full-reset-makes-q-masa-negative-regular
requires:
  - translation-symmetrized-full-schur-reset
  - full-q-masa-forgets-selectors-retains-branches
---

The selector translations in `Rhat_f` split the representation into the
`2^k` equal-dimensional selector sectors `H_x`. It is enough to show that on
every `H_x`, every negative character of `K_f` occurs with multiplicity
`2n`.

First suppose `f(x)=1`. By `(TFS5)`, `H_x` contains `2n` copies of the
unique full-packet simple of dimension `2D`. On that simple, the commuting
involutions `q_1,...,q_N,q_(N+1)` form a maximal Pauli MASA. Its restriction
is the direct sum of all `2D` characters with `J=-1`, each once. Thus each
negative `K_f` character occurs `2n` times on `H_x`.

Now suppose `f(x)=0`. The same formula gives `n` copies of each of four
full-packet simples of dimension `D`. The four simples are indexed by the two
signs of the central relative generators `q_(N+1)` and `p_(N+1)`. For either
fixed `q_(N+1)` sign there are two choices of the invisible `p_(N+1)` sign.
Each choice restricts under `q_1,...,q_N` to every one of the `D` negative
Pauli-MASA characters once. Hence each full `K_f` character again occurs
`2n` times on `H_x`.

Summing the identical restriction over all `2^k` selector sectors gives
multiplicity `2^k(2n)=2^(k+1)n` for each negative `K_f` character, proving
`(FQR1)`. The dimension check is

```text
(2D) 2^(k+1)n = 2^(k+2)Dn,
```

which is exactly the total dimension of the reset-ray representation.

