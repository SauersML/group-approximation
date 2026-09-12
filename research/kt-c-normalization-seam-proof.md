---
rg: 2
id: kt-c-normalization-seam-proof
kind: route
title: Apply the amalgam normal form and the regular trace to the mixed C-normalization rows
target: kt-c-normalization-is-the-first-finite-normalizer-seam
requires:
  - kt-one-compressor-and-sl3-normalizer-lifts-paste
  - kt-two-positive-compressors-generate-full-obstruction
---

The strict compressor `A` has infinite order, whereas `C` has order three,
so `C notin <A>`.  Also `Gamma cap <A>={1}` by the external projection, and
`alpha_C` is an automorphism of `Gamma`.  Hence, for every nonidentity
`gamma in Gamma`, all four syllables of

```text
C | gamma | C^(-1) | alpha_C(gamma)^(-1)
```

lie outside the amalgamated subgroup and alternate between `S` and `H_A`.
The normal-form theorem for free products with amalgamation says that this
is a reduced nonidentity word in `P_A`.

In the actual semidirect product `G`, conjugation by `C` acts on polynomial
coefficients by the variable cycle, so the same word is one.  This proves
the kernel assertion.  Finally `(KPA3)` is trace-correct on every nonidentity
element of `P_A`, whence

```text
||u(w_gamma)-1||_2^2
 =2-2 Re tau(u(w_gamma))=2.
```

Property `(T)` implies finite generation of the discrete group `Gamma`.
Imposing `(KCS2)` on one finite generating set therefore imposes the
`C`-normalization identity on every element of `Gamma`.
