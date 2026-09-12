---
rg: 2
id: julia-derivation-rank-fold-proof
kind: route
title: Quotient the Julia gauge and telescope generator commutator ranks
target: julia-derivation-rank-controls-fold
requires: []
---

If `W in sigma(F)'`, then

```text
(WV)^*sigma(f)(WV)=V^*sigma(f)V,                         (JDP1)
[sigma(x),WV]=W[sigma(x),V].                             (JDP2)
```

Equation `(JDP1)` proves that the vertex pair is unchanged and `(JDP2)`
proves gauge invariance of `(JDG3)`.  Taking `V=1` and `W=-1` proves the
rank variation example and shows directly that `(JDG2)` has no fold
content.

For `a,b in F`,

```text
[sigma(ab),V]
 =sigma(a)[sigma(b),V]+[sigma(a),V]sigma(b).             (JDP3)
```

Also `rank([sigma(x^(-1)),V])=rank([sigma(x),V])`.
Induction on word length therefore gives

```text
rank([sigma(f),V]) <= |f|_X R_X(sigma,V).                (JDP4)
```

A second-copy syllable differs from its folded first-copy syllable by

```text
V^*sigma(f)V-sigma(f)=V^*[sigma(f),V].                   (JDP5)
```

Telescoping a product for `w` and using rank subadditivity gives `(JDG4)`.
For `w in ker(fold)`, `rho(w)-1` is the difference of two unitaries, hence
has operator norm at most `2`.  A rank-`s` matrix of operator norm at most
`2` has squared normalized Hilbert--Schmidt norm at most `4s/d` and
normalized trace modulus at most `2s/d`.  Together with `(JDG4)` this proves
`(JDG5)--(JDG6)`.
