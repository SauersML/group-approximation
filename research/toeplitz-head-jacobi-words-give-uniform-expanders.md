---
rg: 2
id: toeplitz-head-jacobi-words-give-uniform-expanders
kind: claim
title: Toeplitz heads realize the binary Jacobi expander tower by polynomial-length words
distinct_from:
  self-similar-clifford-quantum-expander-tape: that demands level conjugates of fixed templates in a dedicated self-similar presentation; this realizes the same uniform expanders by polynomial-length derived words, which is sufficient for the polynomially weighted doubling recurrence.
  truncated-polynomial-binary-weyl-expander-tower: that constructs the abstract finite Jacobi models and proves their uniform adjoint gap; this embeds all those finite models into one fixed finitely generated property-T group with controlled word complexity.
  toeplitz-finite-head-centralizes-deep-tail: that supplies matrix heads and a commuting recursive tail; this installs the specific nested Heisenberg groups and their relative-Kazhdan normalizers in those heads.
---

Let `T=F_2<x,y | yx=1>` and fix `r>=4`. In the fixed finitely presented
property-`(T)` Steinberg group

```text
Gamma_T=St_r(T)
```

there are nested finite Pauli subgroups

```text
P_1<=P_2<=...,
```

a common central involution `J`, and, for every `n`, words

```text
g_(1,n),...,g_(D,n)
```

of length polynomial in `n` such that:

1. the `J=-1` spin module of `P_n` has dimension `2^n`, and
   `P_(n+1)` restricts as the old spin module tensored with one Pauli qubit;
2. conjugation by the `g_(j,n)` on `P_n/Z(P_n)` is the fixed relative-Kazhdan
   action from `truncated-polynomial-binary-weyl-expander-tower`;
3. on every `J=-1` spin block, their lazy adjoint channel has one gap
   `1-lambda>0` independent of `n`; and
4. the finite Heisenberg, conjugacy, and one-cell inclusion relations used at
   level `n` have derivations from one fixed finite presentation of
   `Gamma_T` of polynomial size in `n`.

Thus normalized-HS defect in the fixed presentation induces at most a
polynomially growing defect in the level-`n` expander checks. This is exactly
the loss allowed by `(SDL2)`, since it is later weighted by `2^(-n)`.

The construction uses derived words rather than literal stable-letter
conjugates. It therefore does not establish
`self-similar-clifford-quantum-expander-tape` as stated.  Moreover the
canonical spin-block gap does not by itself supply the representation-uniform
interface needed by `uniform-relative-clifford-tape-cell`:
`normalizer-multiplicity-twist-breaks-prefix-expander-rounding` shows that
arbitrary representations may twist the normalizer words on the spin
multiplicity.  The twist-free consequence retained from the same head is the
polynomial coordinate-Pauli interface in
`toeplitz-coordinate-paulis-localize-relative-cells-and-grams-polynomially`.
