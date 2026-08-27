---
rg: 2
id: small-trace-rank-one-quarantine
kind: claim
title: Small trace can be shattered into gap-trivial blocks at linear HS boundary cost
distinct_from:
  rank-one-lift-perturbation-gap-no-go: That constructs a vanishing-rank almost-central direction that defeats a coarse finite-level gap; this shows that once such a direction is isolated inside a small-trace projection, refining that projection into rank-one atoms is cheap in the global normalized-HS metric.
  bounded-low-gap-witness-gives-balanced-cut: That extracts a balanced almost-invariant cut from a bounded low-gap witness; this handles the complementary small-trace region after a cut or spike support has already been identified.
---

Let `(M_d,tau)` have normalized trace, let `e in M_d` be a projection, and
let `u_1,...,u_m` and `v_1,...,v_r` be unitaries.  Write any orthogonal
rank-one decomposition

```text
e = q_1 + ... + q_k.
```

Then for every `s`,

```text
sum_(j=1)^k ||[u_s,q_j]||_2^2 <= 2 tau(e).
```

Every rank-one corner has the scalar adjoint Poincare inequality with
**arbitrary** gap constant: for every `lambda>0`, every `s`, and every
self-adjoint `x in q_j M_d q_j`,

```text
sum_s ||(q_j u_s q_j)x - x(q_j u_s q_j)||_(2,q_j)^2
  >= lambda^2 ||x - tau_(q_j)(x) q_j||_(2,q_j)^2.
```

Both sides are zero because `q_j M_d q_j = C q_j`.

If `e != 0`, then for every compressor `v_a` and every two rank-one atoms
`q_j,q_l <= e`,

```text
||v_a q_j v_a^* - q_l||_2 <= sqrt(2/d) <= sqrt(2 tau(e)),
tau(q_l)=tau(q_j)=1/d.
```

Thus a region of total trace `eta` can be quarantined into target-compatible
rank-one fine blocks with at most `2 eta` total generator-boundary energy per
generator and `sqrt(2 eta)` pointwise compressor drift.  The estimates do not
require the region itself to be invariant, nor do they require a finite-level
centralizer.  If `e` lies under an already chosen coarse projection, the
rank-one atoms refine that coarse block and so preserve nesting.

For `hs-expander-block-decomposition`, this means that a **known**
small-trace spike region is not itself an obstruction to the requested block
gap.  The remaining difficulty is global: one must isolate all bad spiky
directions inside a region whose *total* trace is `o(1)` (and do so
compatibly with the nested coarse/fine construction).  A naive iterative
peeling can encounter fresh tiny directions and accumulate order-one trace;
this lemma does not provide a summability potential.
