---
rg: 2
id: bcv-honest-compression-amplifies-readable-closure
kind: claim
title: Honest BCV compression block-amplifies the source readable translate algebra
distinct_from:
  bcv-question-reduction-retains-readable-closure: that proves the tensor inclusion only at the bare honest Question Reduction stage; this follows the inclusion through the complete Question Reduction, Answer Reduction, anchoring, detyping, and Parallel Repetition pipeline.
  bcv-halt-completeness-has-computable-readable-factor-bound: that asks whether some perfect strategy has a total machine-computable bound; this concerns only the strategy produced by the published completeness pipeline.
  computable-bcv-halt-bound-diagonalizes-to-finite-readable-gap: that assumes a uniform existential bound and extracts a NONHALT gap witness; this supplies a lower bound on one explicit HALT-side construction.
---

Let `V` be a `lambda`-bounded tailored normal-form verifier, let `n` be
in the range of the BCV compression theorem, and let `S` be a perfect
finite-dimensional signed-permutation ZPC strategy for `V_(2^n)`. Follow
the particular perfect-completeness constructions in BCV Question Reduction,
Answer Reduction, and Parallel Repetition to obtain

```text
HC_n(S)
```

for `Compress(V,lambda)_n`. Put

```text
k(n)=2^(lambda n),
```

which is the Pauli parameter in the Question Reduction call. Under the
natural sequence of strategy embeddings,

```text
ell^infinity(F_2^k(n)) tensor D_infinity(S)
    subseteq D_infinity(HC_n(S)).                         (HCA1)
```

In particular,

```text
dim D_infinity(HC_n(S))
    >= 2^k(n) dim D_infinity(S).                          (HCA2)
```

Thus neither honest Answer Reduction nor the honest Parallel Repetition
wrapper resets the readable complexity introduced by the Pauli packet. The
claim makes no assertion about perfect strategies not obtained from this
published forward construction.
