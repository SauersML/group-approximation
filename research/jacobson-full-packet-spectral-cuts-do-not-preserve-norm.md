---
rg: 2
id: jacobson-full-packet-spectral-cuts-do-not-preserve-norm
kind: claim
title: Exact whole-packet symmetry and vanishing relative commutator rank do not give operator-norm spectral cuts
distinct_from:
  jacobson-shift-surviving-head-has-a-tracial-core: that obtains Hilbert-Schmidt compression with a surviving mark; this gives an explicit obstruction to upgrading that type of spectral cut to operator norm.
artifacts:
  - research/artifacts/jacobson-full-packet-spectral-cuts-do-not-preserve-norm-2026-09-08.md
---

There are finite complex regular representations, nontrivial marked
involutions, a full diagonal `GL_3(F_2)` subgroup `D`, cyclic block
shifts `T`, and positive contractions `e_N` such that

```text
[e_N,D]=0,             ||[e_N,T]|| <= 1/N,
e_N p_w=p_w,           rank(e_N) < 2 rank(p_w).
```

Every nonzero spectral cut `q=1_[theta,1](e_N)`, `0<theta<=1`,
satisfies `||[q,T]|| >= sqrt(167/168)`. For thresholds in
`[1/4,3/4]`, the commutator rank divided by the marked support rank
tends to zero. Averaging over the entire finite subgroup `D` fixes
these cuts exactly and therefore does not repair the norm error.

These examples test the spectral-cut promotion step. They do not
satisfy all one-sided Jacobson packet and mixed-word relations and
do not refute the coherent matrix gap.

DERIVATION
jacobson-finite-regular-block-cut-counterexample-proof
