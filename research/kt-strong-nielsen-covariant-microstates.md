---
rg: 2
id: kt-strong-nielsen-covariant-microstates
kind: claim
title: Strong covariant microstates exist for the Kun--Thom affine Nielsen action
distinct_from:
  kt-double-mixed-word-trace-selection: that asks only for normalized-Hilbert--Schmidt mixed moments of the two amalgam vertices; this asks for operator-norm strong convergence of the explicit free-radical covariant pair.
  finite-dimensional-nielsen-cocycle-models-kill-mark: that rules out exact finite-dimensional covariant pairs; this permits genuinely approximate actor tables and asks whether they strongly converge.
  kt-double-reduced-cstar-is-mf: that is the intrinsic reduced-C-star formulation; this is the equivalent concrete two-coordinate microstate package exposed by the split Nielsen normal form.
artifacts:
  - research/artifacts/kt-double-mf-trace-literature-audit-2026-08-30.md
---

Use `X,o,N,alpha` from `kt-double-is-nielsen-semidirect-product`.  There are
dimensions `d_n` and maps

```text
U_n:G->U(d_n),             V_n:X->U(d_n),       V_n(o)=1,  (SNM1)
```

with the following properties.

1. The actor law holds pointwise in operator norm:

   ```text
   ||U_n(gh)-U_n(g)U_n(h)|| ->0.                         (SNM2)
   ```

2. The affine Nielsen covariance holds pointwise in operator norm:

   ```text
   ||U_n(g)V_n(x)U_n(g)^*
       -V_n(gx)V_n(go)^*|| ->0.                          (SNM3)
   ```

3. Extend `V_n` uniquely to a homomorphism
   `Vhat_n:N->U(d_n)` using the free basis, and put

   ```text
   W_n(a,g)=Vhat_n(a)U_n(g).                             (SNM4)
   ```

   For every finite family `(a_j,g_j)` and coefficients `c_j`,

   ```text
   ||sum_j c_j W_n(a_j,g_j)||
     ->||sum_j c_j lambda_D(a_j,g_j)||.                  (SNM5)
   ```

4. The normalized traces converge to the regular character:

   ```text
   tr_(d_n)(W_n(a,g))->1_[a=1 and g=1].                 (SNM6)
   ```

Equations `(SNM2)--(SNM3)` make `(W_n)` an operator-norm approximate
representation of `N semidirect_alpha G`; `(SNM5)` is the missing strong
reduced-norm condition.  This package is equivalent to
`kt-double-reduced-cstar-is-mf`.

The exact-action specialization is impossible.  By
`kt-nielsen-models-have-maximal-exact-rounding-gap`, every package above is
asymptotically at operator-norm distance `2` on one fixed radical generator
from every exact finite-dimensional equivariant model.  Thus the word
"approximate" in `(SNM2)--(SNM3)` is load-bearing.

## Attempts

1. **Exact finite-dimensional actor actions.**  Feed exact covariant models
   into an ambient strong-crossed-product theorem.  This dies at
   `kt-nielsen-models-have-maximal-exact-rounding-gap`: exact covariance
   kills the fixed mark, while `(SNM5)` forces its distance from the identity
   to tend to `2`.
2. **Separable-edge finite quotients.**  Apply the double theorem of
   Gao--Kunnawalkam Elayavalli--Manzoor--Patchell.  The Kun--Thom edge is not
   separable, and `kt-finite-image-relative-edge-models-are-impossible`
   shows that arbitrary weighted finite-image blocks still cannot recover
   the edge expectation.
3. **Profinite regular coordinates.**  Use the already available symmetric
   full-amalgam model.  This dies before the Nielsen assembly:
   `kt-shulman-profinite-vertex-model-is-nontempered` gives a fixed Kesten
   norm gap on one vertex.

What remains is deliberately not deferred: construct genuinely approximate
operator-norm actor/covariance tables satisfying `(SNM5)`, or prove that the
infranormal Kazhdan geometry forces their fixed marked generator to collapse.
