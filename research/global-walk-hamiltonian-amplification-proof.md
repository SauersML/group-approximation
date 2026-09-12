---
rg: 2
id: global-walk-hamiltonian-amplification-proof
kind: route
title: Compress the expander transfer operator and retain both walk endpoints
target: global-walk-linearly-amplifies-hamiltonian-energy
requires: []
artifacts:
  - research/artifacts/qpcp-global-walk-amplification-2026-09-11.md
  - research/artifacts/check-qpcp-global-walk-2026-09-11.py
  - research/artifacts/qpcp-global-walk-replay-2026-09-11.json
---

Sections 1--3 of the artifact give the complete proof. On the tensor-copy
space, `D_j=sum_v |v><v| tensor (I-h_v)^(j)` is a positive contraction,
`U psi=u tensor psi`, `P=UU*`, and `T=M tensor I`. Then
`U*D_j^2U<= (1-epsilon)I`, while
`T^2<=lambda^2 I+(1-lambda^2)P`. Consequently

```text
||D_jT||^2<=1-(1-lambda^2)epsilon,
||D_jU||^2<=1-epsilon.
```

The complete accepting walk operator is exactly
`U*D_1 T D_2 ... T D_tU`. Retain the two endpoint factors and bound the
`t-2` interior factors to obtain the target lower energy bound. Positivity
of the tensor summands converts the operator-norm bound into a ground-energy
bound for all states. A ground-state tensor power and the scalar union
bound give completeness. The rational simplification and all size/locality
claims are proved explicitly in the artifact.
