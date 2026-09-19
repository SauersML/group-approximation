---
rg: 2
id: full-conjugation-table-cancels-router-multiplicity-proof
kind: route
title: Pull the router error into the packet commutant and telescope a balanced word
target: full-conjugation-table-cancels-router-multiplicity
requires: []
---

Put `D=pi(a)^*C`.  For every generator `s in S`, bi-invariance of normalized
Hilbert--Schmidt norm gives

```text
||D pi(s) D^* - pi(s)||_2
 = ||C pi(s) C^* - pi(a s a^(-1))||_2
 <= eta.
```

Multiplying on the right by `D` proves `(FCT2)`.  Choose once and for all an
`S`-word for each element of the finite group `K`, and let `diam_S(K)` be the
largest chosen length.  A word telescope then gives

```text
||[D,pi(k)]||_2 <= diam_S(K) eta                    (1)
```

for every `k in K`.

Substitute `C=pi(a)D` and `C^*=D^*pi(a)^*` into `W(C)`.  Move every occurrence
of `D` or `D^*` to the right through the intervening constant factors.  Each
crossing costs at most `(1)`, and the number of crossings is bounded by a
constant determined only by the fixed word `W`.  Because the exponent sum of
the router letter is zero, all transported `D,D^*` factors cancel.  What
remains is exactly `pi(W(a))`.  Summing the crossing errors proves `(FCT3)`;
for example one may take

```text
L_(K,S,W)=N_cross(W) diam_S(K).
```

Equivalently, when `W` is already written as a product of constants and
conjugates `t k t^(-1)`, telescope `(FCT1)` over the chosen word for `k` and
then over the finitely many conjugate atoms.  This gives the same
dimension-free conclusion without explicitly moving `D`.

