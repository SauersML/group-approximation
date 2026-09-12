---
rg: 2
id: atlas-rankwise-gap-is-ultraproduct-obstruction
kind: claim
title: Rankwise atlas gaps are positive, and their uniform collapse is exactly the matrix-ultraproduct obstruction
distinct_from:
  atlas-exact-matrix-zero-set-is-a-finite-quotient-test: that classifies exact zeros at one finite dimension using Malcev; this identifies the sole remaining failure mode across unbounded dimensions.
  atlas-a4-root-energy-ellipse-ceiling: that states the final scalar contradiction; this isolates its equivalent uniform residual gap before evaluating the ellipse.
---

For `k>=1`, put `rho_k=Reg(A8) tensor I_k`.  For a relative unitary
`U in U(20160k)`, let

```text
epsilon(k,U)
 =max( ||q_19243(U)-1||_2,
       max_(w in the thirty-word packet)||w(U)-1||_2 ),
delta_k=inf_(U in U(20160k)) epsilon(k,U).             (RANK-GAP-1)
```

Assume `Gamma_A4` has no nontrivial finite quotient.  Then:

1. `delta_k>0` for every fixed `k`.
2. The following are equivalent:

   ```text
   inf_(k>=1) delta_k=0;                               (RANK-GAP-2)
   ```

   ```text
   the thirty packet relations and q_19243 have an exact
   regular-margin solution in a tracial matrix ultraproduct. (RANK-GAP-3)
   ```

3. If `(RANK-GAP-2)` holds, every witnessing sequence has unbounded
   multiplicity after passage to a subsequence.

Consequently a dimension-independent quantitative Malcev separation estimate

```text
epsilon(k,U)>=delta>0       for every k,U              (RANK-GAP-4)
```

is not an intermediate consequence of ordinary residual finiteness.  It is
exactly the negation of the remaining matrix-ultraproduct zero-set statement,
equivalently the positive joint residual gap already isolated in
`atlas-a4-root-energy-ellipse-ceiling`.

Malcev's theorem supplies the rankwise assertion only after an **exact**
finite-dimensional zero is given: it separates a nonidentity element of the
resulting finitely generated linear image.  It gives no uniform correction
from an approximate tuple to such an exact image.  Any bound achieving
`(RANK-GAP-4)` would therefore already be the required dimension-free
HS-stability/CE-sensitive input, rather than a quantitative refinement of the
finite-quotient argument.
