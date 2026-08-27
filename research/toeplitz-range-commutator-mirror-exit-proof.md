---
rg: 2
id: toeplitz-range-commutator-mirror-exit-proof
kind: route
title: Exit the Toeplitz range commutator through the mirror identity
target: toeplitz-range-commutator-has-a-balanced-mirror-exit
requires:
  - fanizza-compressed-unitary-has-guarded-rank-floor
  - diagonal-difference-shift-propagates-pauli-incidence
  - central-corner-block-is-not-a-group-word
---

Decompose the finite carrier as

```text
F direct_sum H direct_sum C direct_sum K,
```

with `dim(C)=dim(H)`.  Take `E=F+H`, let `T` fix `F,K` and swap `H,C`, and
put `Q=TET^*=F+C`.  This proves `(TRC2)--(TRC5)` directly.  Since
`tau(Q)=tau(E)`, expanding both traces in the four joint cells proves
`(TRC6)`.

For the word blindness, the three characters in `(TRC7)` have trivial
intersection of kernels in `C_2 times C_2`.  Thus the corresponding
three-cell representation is faithful, so every word vanishing there is a
group identity and also vanishes on the missing fourth character.

Finally tensor the construction with the exact reset ray and an independent
old-spin Pauli factor.  This preserves all local type and diagonal-difference
incidences.  Removing `C` requires the supported zero block `(TRC8)`, whose
additive controlled-corner character is not supplied by the reflection
commutator.
