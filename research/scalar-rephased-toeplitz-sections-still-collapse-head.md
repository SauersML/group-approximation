---
rg: 2
id: scalar-rephased-toeplitz-sections-still-collapse-head
kind: claim
title: Scalar rephasings of Toeplitz finite sections still collapse the Jacobson head uniformly
distinct_from:
  binary-gl-finite-sections-have-no-projective-k2-phase: that proves every projective finite-section representation linearizes; this controls the remaining scalar one-cochain after linearization
  toeplitz-folner-compressions-cannot-retain-jacobson-head: that proves exact equality for ordinary finite-group representations; this allows arbitrary generator-by-generator scalar phases
  jacobson-property-t-and-finite-k-do-not-exactify-the-head: that explains why finite K alone does not control arbitrary approximate representations; this uses finite K only inside the specific Toeplitz finite-section ansatz
---

Use a fixed Tietze-expanded Steinberg presentation containing the scalar
subgroup `K=GL_28(F_2)` and the five named roots

```text
C=x_13(1),
U=x_12(T),          V=x_23(S),
U'=x_14(S),         V'=x_43(T).
```

For every `N`, substitute the truncated shifts `S_N,T_N), compose
with any ordinary unitary representation of `GL_(28N)(F_2)), and allow
an arbitrary scalar phase on every named generator. Arbitrary direct sums
of such sectors, with sector-dependent phases, are also allowed.

There is a constant `L<infinity), depending only on the fixed
presentation and not on `N), the representation, or its multiplicities,
such that

```text
|| C[U',V']-I ||_2
 <= L delta,                                             (SRT1)
```

where `delta` is the maximum defect of the fixed presentation relators.

The word on the left is the Jacobson head:

```text
C[U',V']=x_13(1)x_13(ST)=x_13(1-ST).                    (SRT2)
```

Thus neither genuine projective multipliers nor arbitrary choices of
their scalar lifts repair the Toeplitz finite-section construction.
Every scalar-rephased finite section has a dimension-free head modulus.

The scope remains explicit. The theorem covers all finite-section root
matrices followed by projective representations and arbitrary scalar
one-cochains. It does not cover perturbations which change the root
unitaries by nonscalar operators or approximate representations not
obtained from the truncated Toeplitz matrices.

DERIVATION
perfect-scalar-root-and-two-commutators-proof
