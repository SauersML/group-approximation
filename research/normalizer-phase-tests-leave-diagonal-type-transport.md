---
rg: 2
id: normalizer-phase-tests-leave-diagonal-type-transport
kind: claim
title: Normalizer phase tests leave diagonal type transport completely free
distinct_from:
  fourier-normalizer-words-control-block-gram-leakage: that gives the exact positive control of off-type block-Gram products; this identifies the complementary diagonal population kernel and gives exact zero-energy countermodels.
  hadamard-does-not-semidir-independent-selector-blocks: that rules out classical semidirect transport of independent selector blocks; this is a purely analytic limitation of every finite family of phase-normalizer commutators, even when all phase cuts already exist.
  global-covariance-misses-capacity-compression: that shows an uncompressed covariance row leaves an uncontrolled commutator after compression; this contrasts commutator and phase-matching tests on already authenticated source and target partitions.
---

**ESTABLISHED SHARP LIMIT.**  Let `(F_j)` and `(E_i)` be finite orthogonal
partitions of `1`, and let `P` be unitary.  Put

```text
p_(ij)=||E_iPF_j||_2^2.                                (NPT1)
```

The matrix `(p_(ij))` is a nonnegative transport table with row and column
margins `tr(E_i)` and `tr(F_j)`.  Fourier normalizer commutators control only
the off-diagonal coherences

```text
E_iPF_jP^*E_k,                 i!=k.                   (NPT2)
```

They do not control which diagonal cells `(i,j)` carry the population in
`(NPT1)`.  Indeed, if every transported projection `PF_jP^*` commutes with
every `E_i`, then all phase-normalizer commutators vanish for every choice of
phase codes on the two partitions, while the table `(p_(ij))` may have mass
on any cell allowed by its margins.

In particular, take `S,C` of equal positive trace and choose `P` with
`PSP^*<=I-C`.  For the binary source and target partitions
`(S,I-S)` and `(C,I-C)`, all normalizer commutators vanish whenever `PSP^*`
is a sum of target atoms, but

```text
||(I-C)PS||_2^2=tr(S)>0.                               (NPT3)
```

Consequently Fourier normalizer words can remove coherent cross-type Gram
leakage, but a GTC4 compiler must additionally enforce **phase matching**.
For authenticated tags this is measured by a covariance defect
`PD_source P^*D_target^*-I`, not by commutation of
`PD_source P^*` with `D_target`.
