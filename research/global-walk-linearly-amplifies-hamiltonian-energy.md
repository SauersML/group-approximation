---
rg: 2
id: global-walk-linearly-amplifies-hamiltonian-energy
kind: claim
title: A global expander walk gives linear tensor amplification of Hamiltonian energy
artifacts:
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
1-(1-epsilon)[1-(1-lambda^2)epsilon]^((t-2)/2)
 <= lambda_min(G_t(H)) <= min{1,t epsilon}.
```

In particular, for `lambda<=1/2` and even `t`,

```text
lambda_min(G_t(H))>=min{(3t+2)epsilon/16,1/2}.
```

The construction multiplies locality and site count by at most `t`, keeps
local dimension, and replaces `m` terms by `m d^(t-1)` terms counted with
edge multiplicity for a `d`-regular graph. It preserves the positive-
contraction property, and preserves projectivity when present. It works
for entangled states across copies and has no commuting-layer hypothesis.

This is a self-contained positive-contraction sharpening and application
of known operator amplification along expander walks, not a priority claim.
Growing locality remains the unresolved composition problem.
