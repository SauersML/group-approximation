---
rg: 2
id: stw22-chern-l2-small-commutator-width-proof
kind: route
title: Kill all lower-left blocks at one point by the top Chern class
target: stw22-chern-l2-small-unbounded-commutator-width
requires: []
artifacts:
  - research/artifacts/stw22-chern-commutator-width-audit-2026-08-31.md
---

Write `E_s=1+F_s` with `F_s=L_s^(+s)`. Relative to this splitting, write

```text
z_j = [ a_j  b_j ]
      [ c_j  d_j ].
```

The lower-left corner `c_j` is a section of `F_s`. Hence
`(c_1,...,c_ell)` is a section of `F_s^(+ell)=L_s^(+s ell)`. If
`ell<=s`, then `s ell<=s^2`, and with `u=c_1(L_s)` the top Chern class is

```text
c_(s ell)(L_s^(+s ell)) = u^(s ell) != 0
    in H^(2 s ell)(CP^(s^2); Z).
```

Therefore this section has a zero, say at `x`. At `x`, all `c_j(x)=0`.
Compressing a self-commutator to the trivial-line corner gives

```text
p_s (z_j^* z_j - z_j z_j^*) p_s
  = c_j^* c_j - b_j b_j^*
  = - b_j b_j^* <= 0.
```

Since `p_s h_s p_s=p_s`, the trivial-line compression of
`h_s-sum_j[z_j^*,z_j]` is at least the identity on that line. Its operator
norm is therefore at least one, proving `(CW-2)`.

The trace and `2`-norm assertions are fibrewise: `p_s` and `q_s` are
orthogonal rank-one projections in every `M_(s+1)` fibre. Thus every
tracial state gives them the same value `1/(s+1)`, while
`h_s^2=p_s+q_s`. This proves `(CW-1)` and closes the claim.
