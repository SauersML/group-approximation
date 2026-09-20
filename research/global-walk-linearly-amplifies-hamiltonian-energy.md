---
rg: 2
id: global-walk-linearly-amplifies-hamiltonian-energy
kind: claim
title: A global expander walk gives linear tensor amplification of Hamiltonian energy
artifacts:
  - research/artifacts/qpcp-strengthened-amplification-2026-09-20.md
  - research/artifacts/check-qpcp-strengthened-amplification-2026-09-20.py
  - research/artifacts/qpcp-strengthened-amplification-replay-2026-09-20.json
  - research/artifacts/qpcp-global-walk-amplification-2026-09-11.md
  - research/artifacts/check-qpcp-global-walk-2026-09-11.py
  - research/artifacts/qpcp-global-walk-replay-2026-09-11.json
distinct_from:
  bmvz-iterable-tensor-gap-amplification: that walks separately within commuting layers and proves a square-root gain; this walks over all clauses and gives a linear gain without a layer assumption, using positive transfer operators and existing operator-amplification prior art.
  ordinary-gap-amplification-grows-locality: that concerns the detectability-lemma construction; this specifies a global tensor-walk construction and its quantitative energy bounds, with arbitrary positive-contraction terms.
---

For `H=(1/m)sum_v h_v`, `0<=h_v<=I`, and
`epsilon=lambda_min(H)`, let `M` be a regular undirected transition
matrix on the whole clause list with `||M-|u><u|||<=lambda<1`,
where `u` is the uniform unit vector. For a stationary walk with `t>=2`
vertices define

```text
G_t(H)=E_(v_1,...,v_t) [I-tensor_(j=1)^t(I-h_(v_j))].
```

Then

```text
1-(1-epsilon)[1-(1-lambda)epsilon]^(t-1)
 <= lambda_min(G_t(H)) <= min{1,t epsilon}.
```

For `B_t(lambda)=1+(t-1)(1-lambda)`, this is at least
`B_t(lambda) epsilon/(1+B_t(lambda) epsilon)`. In particular, for
`lambda<=1/2` and every integer `t>=2`,

```text
lambda_min(G_t(H)) >= B_t epsilon/(1+B_t epsilon),  B_t=(t+1)/2.
```

The construction multiplies locality and site count by at most `t`, keeps
local dimension, and replaces `m` terms by `m d^(t-1)` terms counted with
edge multiplicity for a `d`-regular graph. It preserves the positive-
contraction property, and preserves projectivity when present. It works
for entangled states across copies and has no commuting-layer hypothesis.

The September 20 positive-sandwich proof supersedes the weaker September 11
estimate. It uses `T=|T|^(1/2) sign(T) |T|^(1/2)` and includes negative
transition eigenvalues; no laziness or even-length restriction is imposed.

This is a self-contained positive-contraction sharpening and application
of known operator amplification along expander walks, not a priority claim.
Growing locality remains the unresolved composition problem.
