---
rg: 2
id: bcv-every-perfect-compression-amplifies-readable-closure
kind: claim
title: Every attained-perfect BCV compressed strategy contains the full Question Reduction Pauli amplification
distinct_from:
  bcv-honest-compression-amplifies-readable-closure: that follows BCV's chosen forward completeness strategy; this decodes an arbitrary attained-perfect final compressed strategy backward through repetition, detyping, anchoring, Answer Reduction, and Question Reduction.
  bcv-every-perfect-question-reduction-amplifies-readable-closure: that treats the bare Question Reduced game; this proves that none of the surrounding compression wrappers can erase its exact tensor inclusion.
  bcv-perfect-answer-reduction-decodes-double-cover: that supplies the exact Answer Reduction inverse used here but does not supply the Pauli factor.
---

**ESTABLISHED (attained value one).** Let `V` be a `lambda`-bounded
`h`-level tailored normal form verifier, let `n>=C(h)`, and put

```text
V'_n=Compress_h(V,lambda)_n,
k(n)=2^(lambda n).
```

For every attained-perfect finite-dimensional signed-permutation ZPC
strategy `S` for `V'_n`, there is a perfect signed-permutation ZPC strategy
`T` for the supported part of `V_(2^n)` and a monomial identification

```text
W:H_S -> ell^2(F_2^k(n)) tensor H_T
```

such that

```text
W D_infinity(S) W^*
  contains ell^infinity(F_2^k(n)) tensor D_infinity(T).  (UCA1)
```

Unsupported formal vertices may be filled with trivial measurements. In
particular,

```text
dim H_S = 2^k(n) dim H_T,

dim D_infinity(S)
  >= 2^k(n) dim D_infinity(T)
  >= 2^(2^(lambda n)).                                   (UCA2)
```

All inverse steps before the Question Reduction normal form act in the
original matrix algebra and only discard, restrict, or coarse-grain
measurements. The only change of basis is the monomial Pauli identification,
so the ZPC typing and the readable-translate inclusion are literal.

The statement concerns attained perfect finite-dimensional strategies.
A value-one supremum without attainment gives an analogous tracial
ultraproduct statement, not a finite-dimensional strategy `T`.

The wrapper audit and proof are
`bcv-perfect-compression-backward-amplification-proof`.
