---
rg: 2
id: orthogonal-frozen-support-surgery-proof
kind: route
title: Sum smooth corrections absolutely and frozen cuts orthogonally
target: orthogonal-frozen-support-surgery-has-square-root-rank-cost
requires: []
artifacts:
  - research/artifacts/flexible-curvature-surgery-audit-2026-09-05.md
---

Set

```text
A_(k,s)=W^k_s-U^k_s,
B_(k,s)=U^(k+1)_s-W^k_s=(I-W^k_s)P_k.
```

Exact commutation with `P_k` makes the next tuple unitary: it is the
restriction of `W^k_s` to the complementary reducing subspace plus the
identity on `P_k`. It also makes
`B_(k,s)=P_k B_(k,s)P_k`. The latter equality on **both** sides is why
the cut errors have orthogonal matrix supports.

For every finite interval of indices,

```text
||sum_(k=N)^M A_(k,s)||_2 <= sum_(k=N)^M a_k,
||sum_(k=N)^M B_(k,s)||_2^2
 =sum_(k=N)^M ||B_(k,s)||_2^2
 <=4 sum_(k=N)^M tr(P_k).
```

The first estimate uses the triangle inequality. For the second, the
mixed matrix inner products vanish because `P_i P_k=0` when `i!=k`,
and `||I-W^k_s||_op<=2`. Both series are Cauchy under the stated budgets.
Telescoping

```text
U^N_s-U^0_s=sum_(k<N) A_(k,s)+sum_(k<N) B_(k,s)
```

proves convergence and `(OFS1)`. Fixed dimension is used only at the last
step: normalized-HS convergence is ordinary matrix convergence, so the
limit is unitary, and each finite relator word is continuous. The
vanishing defining defects therefore give an exact representation.

In fixed finite dimension, pairwise orthogonality implies that only
finitely many `P_k` can be nonzero. This observation does not imply that
the final nonzero cut has killed the relators; a tail of smooth
corrections can still be needed. Zero cuts allow that tail in the
statement. Conversely, for a finite schedule ending with an exact tuple,
the finite telescoping estimate already gives the same conclusion.

The previously frozen subspaces must stay frozen at every smooth step.
Since the matrices are unitary, acting as identity there also prevents
any mixing with the active complement. Thus all cut supports in the
argument are actual orthogonal projections in one fixed ambient space;
there is no moving-coordinate identification hidden in the sum.

For `(OFS3)`, iterate the assumed repair method with defect bounds
`delta_k=2^(-k)delta`. Its smooth corrections sum to at most `2C delta`,
and monotonicity of `m` bounds the total rank removed by `D_m(delta)`.
The assumptions of `(OFS1)` hold, giving exactly `(OFS3)`. Consequently
the quantitative hypotheses imply a full stability result, including an
exact endpoint, whereas cohomological concentration alone does not
provide these hypotheses.

For completeness, suppose the method is expressed in the active
dimension rather than the original dimension. Let the active fraction at
step k be `q_k`, and let the original-dimension defect bound be
`delta_k`. Since the frozen block is a trivial representation, the
active normalized defect is `delta_k/sqrt(q_k)`. A smooth active
correction of size at most `C delta_k/sqrt(q_k)` has original-normalized
size at most `C delta_k`, so these factors cancel exactly.

As long as `q_k>=1/2`, the newly cut original relative rank is at most

```text
q_k m(delta_k/sqrt(q_k)) <= m(sqrt(2)delta_k).
```

After replacing that block by the trivial representation, a halving of
the defect measured in the *pre-cut active dimension* also halves the
original-normalized defect. The active tuple at the next step is then
the restriction to the remaining complement. If
`D_m(sqrt(2)delta)<1/2`, induction bounds every partial total removed
rank by that quantity. Hence `q_k>1/2` throughout, verifying the premise
of the estimate at every step. Apply `(OFS1)` with cumulative rank
`D_m(sqrt(2)delta)`.

The pre-cut normalization in this paragraph is substantive: after the
support is trivialized, it is still counted for that step's halving
claim. A different normalization must first be converted explicitly.
No application of property `(T)` or cohomology vanishing has been used
to manufacture reducing projections or a repair map.
