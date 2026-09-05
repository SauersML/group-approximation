---
rg: 2
id: regular-component-cohomology-concentration-proof
kind: route
title: Deduce trace-norm concentration from the small-angle curvature correction
target: two-kazhdan-correction-concentrates-normalized-hs-curvature
requires:
  - two-kazhdan-correction-has-quadratic-rank-curvature
artifacts:
  - research/artifacts/parallel-arithmetic-holonomy-2026-09-04.md
---

Apply the required theorem with the target's ordinary all-unitary Hilbert
H2 vanishing hypothesis. Its corrected tuples already have generator
change `O(delta_j)` and defining HS defect `O(delta_j)`. For each fixed
`epsilon>0` it supplies a projection `P_(j,epsilon)` of normalized trace
at most `C_epsilon delta_j^2` with complementary HS error at most
`epsilon delta_j`.

For each corrected defining error `E_j`, normalized Schatten Holder gives

```text
||E_j||_1 <= ||E_j(I-P_(j,epsilon))||_2
             + ||E_j||_2 sqrt(tr(P_(j,epsilon)))
          <= epsilon delta_j + O(sqrt(C_epsilon) delta_j^2).
```

Take limsup after division by delta, then let epsilon tend to zero.
The same tuples therefore satisfy `max_r||E_(j,r)||_1=o(delta_j)`.
Interpolation with the HS bound proves the target's Schatten p statement
for every `1<=p<2`.

For the small-support operator-norm conclusion, put
`a_j=max_r||E_(j,r)||_1/delta_j->0`, choose positive `t_j->0` with
`a_j/t_j->0`, and define

```text
P_j=join_r 1_(|E_(j,r)|>t_j delta_j),   Q_j=I-P_j.
```

Markov's inequality gives `tr(P_j)<=|R|a_j/t_j->0`. The complement is
below every low spectral projection. Each `E_(j,r)` is normal, being
unitary minus identity, so its left and right complementary operator norms
are at most `t_j delta_j`. This is `(KCC3)`. These projections are
different from the fixed-epsilon quadratic-rank projections; this argument
does not give both bounds with the same rank constant.

Finally the target's uniformly vanishing normalized square tails imply
the required theorem's small-angle input condition `(QRC4)`: for every
fixed actual-angle cutoff `t>0`, the normalized cutoff `t/delta_j` tends
to infinity. Its subsidiary conclusion gives HS residual `o(delta_j)`.
No invariant support or infinite correction schedule follows. The artifact
records the original regular-component argument and its iteration limits;
the stronger small-angle theorem now supplies this route directly.
