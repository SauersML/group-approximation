---
rg: 2
id: global-walk-hamiltonian-amplification-proof
kind: route
title: Positive sandwiches of the absolute transfer operator sharpen every walk factor
target: global-walk-linearly-amplifies-hamiltonian-energy
requires: []
artifacts:
  - research/artifacts/qpcp-strengthened-amplification-2026-09-20.md
  - research/artifacts/check-qpcp-strengthened-amplification-2026-09-20.py
  - research/artifacts/qpcp-strengthened-amplification-replay-2026-09-20.json
  - research/artifacts/qpcp-global-walk-amplification-2026-09-11.md
  - research/artifacts/check-qpcp-global-walk-2026-09-11.py
  - research/artifacts/qpcp-global-walk-replay-2026-09-11.json
---

Section 2 of the September 20 artifact gives the complete positive-sandwich
proof, replacing the weaker September 11 estimate. On the tensor-copy space,
`D_j=sum_v |v><v| tensor (I-h_v)^(j)` is positive and contractive,
`U psi=u tensor psi`, `P=UU*`, and `T=M tensor I`. Set
`a=1-epsilon`, `c=1-(1-lambda)epsilon`, `V=|T|^(1/2)`, `J=sign(T)`.
Then `T=VJV`, `||J||<=1`, `|T|<=lambda I+(1-lambda)P`, and

```text
||VD_jV|| <= c,
||VD_jU||^2 = ||U*D_j|T|D_jU|| <= lambda a+(1-lambda)a^2 = ac.
```

The first bound uses equality of the norms of `XX*` and `X*X` for
`X=VD_j^(1/2)` and `||D_j^(1/2)PD_j^(1/2)||=||U*D_jU||<=a`.
The second uses `D_j^2<=D_j` and `U*D_jPD_jU=(U*D_jU)^2`.
The exact accepting operator is `U*D_1 T D_2 ... T D_tU`.
Two endpoints contribute `ac`, `t-2` middle sandwiches contribute
`c^(t-2)`, and sign factors are contractions. Hence `||A_t||<=a c^(t-1)`.
Positivity converts this to ground-energy soundness for all entangled states.
Negative transition eigenvalues and odd `t` are allowed.

A ground-state tensor power and the scalar union bound give completeness.
The rational bound, limiting cases, resource counts and comparison with the
old bound are proved in the artifact. Exact finite replays support the
written proof; they do not formally verify the universal theorem.
