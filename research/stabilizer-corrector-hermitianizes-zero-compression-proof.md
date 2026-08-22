---
rg: 2
id: stabilizer-corrector-hermitianizes-zero-compression-proof
kind: route
title: Swap the source with its backward payload image
target: stabilizer-corrector-hermitianizes-zero-compression
requires: []
---

From `QWQ=0` one has

```text
Q(W^*QW)=(QW^*Q)W=0,
```

so `Q` and `R=W^*QW` are orthogonal.  The restriction `W:R H -> Q H` is
unitary.  Define `V` on `QH direct-sum RH` by this unitary and its adjoint in
the off-diagonal blocks, and take `V=1` on the orthogonal complement.  Then
`V=V^*=V^-1` and `VRV=Q`.

For `S=VW^*`,

```text
SQS^*=V(W^*QW)V=VRV=Q,
SW=V.
```

Since a unitary normalizing a projection commutes with it, `SQ=QS`.
Therefore `QSWQ=S QWQ`, proving both directions of `(SCZ1)--(SCZ2)`.
