---
rg: 2
id: dense-offdiagonal-average-collapse-proof
kind: route
title: Tensor Pauli anticommutation with an orthogonal character table
target: dense-offdiagonal-packet-has-linear-dimensional-average-models
requires:
  - dense-offdiagonal-leavitt-heisenberg-packet
---

Let `K=F_2^n`, and let `D_alpha` be its `D` diagonal character matrices in
the regular basis.  They are commuting involutions and

```text
tr(D_alpha D_beta)=delta_(alpha,beta).
```

On the negative central sector

```text
H_-=C^2 tensor C^D tensor C^2
```

put

```text
J=-I,
X_alpha=P tensor D_alpha tensor I_2,
Y_beta =Q tensor D_beta  tensor I_2,
```

where `P,Q` are Pauli involutions with `PQ=-QP`.  Every cross commutator is
`-I`; hence all unequal complementary Weyl relations hold and precisely the
equal ones fail.

On the equally dimensional positive sector

```text
H_+=C^2 tensor C^2 tensor C^D
```

put

```text
J=I,
X_alpha=(Z tensor I) tensor D_alpha,
Y_beta =(I tensor Z) tensor D_beta.
```

All cross commutators are now `I`, as required when `J=I`.  The Pauli
factors have trace zero and orthogonal mixed factors, while the character
table gives label orthogonality.  Their direct sum has dimension `8D` and
satisfies `(DOA1)`.

On an equal pair the negative half has commutator `-I` instead of `I`, so
the full normalized squared HS defect is `(1/2)·4=2`.  There are `D` such
pairs among `D^2`; the mean squared defect is therefore `2/D`.

