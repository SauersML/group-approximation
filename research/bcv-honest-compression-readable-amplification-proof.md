---
rg: 2
id: bcv-honest-compression-readable-amplification-proof
kind: route
title: Carry the Pauli block algebra through every honest compression wrapper
target: bcv-honest-compression-amplifies-readable-closure
requires:
  - bcv-question-reduction-retains-readable-closure
  - bcv-honest-answer-reduction-retains-readable-closure
---

Start with the restriction-free padded strategy for `V_(2^n)`. Padding
retains the source variables as initial coordinates, so its readable
translate algebra contains `D_infinity(S)`. The Question Reduction
prerequisite gives

```text
ell^infinity(F_2^k(n)) tensor D_infinity(S)
    subseteq D_infinity(QR_k(n)(S)).                      (HCAP1)
```

The algorithmic Question Reduction ends with detyping. The A- and B-copy
vertices in the detyped game carry the same matrices as the corresponding
typed vertices, while the added anchor vertices have answer length zero.
Hence detyping retains `(HCAP1)`.

Next apply BCV's published Answer Reduction completeness construction. Its
extra padding retains initial coordinates and purification preserves the
strategy set exactly. Double cover and oracularization retain isolated
copies. At the PCP stage, equation `(192)` evaluates the multilinear
encoding of each isolated answer function at points of `F_q^S`. For each
original padded coordinate `xi`, evaluation at the Boolean point with
`S_f=xi` recovers that coordinate exactly. Table 3 marks the recovered
`R` field bits readable and the recovered `L` field bits linear.
Therefore every readable projection and every structural unreadable
generator from `(HCAP1)` is a word of the same type in the answer-reduced
strategy. Equivalently, this is the embedding proved by the honest Answer
Reduction prerequisite. Conjugation-word induction shows that the full
algebra in `(HCAP1)` survives Answer Reduction.

Anchoring adds accepting zero-answer vertices and keeps the old vertices. The
following detyping again keeps A- and B-copies of every old measurement.
Finally, the honest `r`-fold Parallel Repetition strategy is the sum of
`r` copies in the sense of BCV Definition 3.47: a generator in the first
coordinate acts as

```text
u tensor 1 tensor ... tensor 1.
```

Readable marginals and unreadable conjugations in that coordinate therefore
embed the entire pre-repetition readable translate algebra in the first
tensor factor. This proves `(HCA1)`.

The SamZ algebra has `2^k(n)` atoms. Tensoring a finite Boolean algebra with
it multiplies the number of atoms, equivalently the dimension, by
`2^k(n)`. A containing Boolean algebra cannot have smaller dimension,
proving `(HCA2)`.
