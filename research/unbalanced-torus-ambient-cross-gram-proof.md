---
rg: 2
id: unbalanced-torus-ambient-cross-gram-proof
kind: route
title: Identify the first lamp cross-Gram with the projective denominator commutator
target: unbalanced-torus-forces-cross-gram-on-ambient-face
requires:
  - unbalanced-torus-extracts-near-central-denominator-coordinate
---

Put

```text
W=H sigma(h)^*.
```

For `c in S_+`, write `c'=h^(-1)c h`.  Exactness of `sigma` gives

```text
W sigma(c) W^*=H sigma(c')H^*.
```

Consequently the overlap energy in `(NCD1)` is exactly

```text
a_+(W)=alpha_+(H).                                     (ACP1)
```

Apply `(NCD2)` with auxiliary unitary `U=T`:

```text
1-|tr([T,H])|^2
 <=K q_C(T)+C_0 eta^2+C_0 alpha_+(H).                  (ACP2)
```

For the commutator convention `[T,H]=THT^*H^*`, the inverse commutator is
conjugate to it:

```text
T^*H^*TH=(TH)^(-1)[T,H](TH).                           (ACP3)
```

Normalized trace is invariant under conjugation, hence

```text
tr(T^*H^*TH)=tr([T,H]).                                (ACP4)
```

Substitute `(ACP4)` into `(ACP2)` to obtain `(ACG2)`.

The proof never decomposes `sigma`, `H`, or `T`.  The arbitrary-block and
operator-Schmidt assertions therefore follow immediately, rather than by
accumulating errors over summands.
