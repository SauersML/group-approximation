---
rg: 2
id: atomic-leavitt-gap-on-nonzero-matrix-corner
kind: claim
title: Every nonzero finite matrix corner has a dimension-free Leavitt defect
distinct_from:
  approximate-relative-leavitt-cell-kills-active-trace: that is a normalized-Hilbert--Schmidt trace estimate whose strength scales with ambient carrier mass; this renormalizes on the selected nonzero corner and obtains an absolute operator-norm gap even at rank one.
  rank-deficient-return-row-has-operator-norm-one: that needs exact coarse and fine packet ranks plus one support-return row; this needs only the diagonal inverse rows and completeness row and does not first expose matrix-unit rank fractions.
  typed-pi-superrank-data-do-not-decode-prescribed-leavitt-carrier: that uses the binary trace inequality as a firewall inside one typed countermodel; this isolates and proves the general m-ary operator-norm theorem on every nonzero finite corner.
artifacts:
  - research/atomic-leavitt-gap-on-nonzero-matrix-corner-proof.md
  - research/artifacts/property-t-free-atomic-leavitt-amr-2026-08-24.md
---

**ESTABLISHED.** Let `p!=0` be a projection in `M_d(C)`, let `m>=2`, and
let

```text
s_i,t_i in p M_d(C) p,                 1<=i<=m.
```

Then

```text
m-1
 <= sum_i ||t_i s_i-p||_op
    + ||sum_i s_i t_i-p||_op.                         (ALG1)
```

Consequently, if all `m+1` displayed defects are at most `epsilon`, then

```text
epsilon >= (m-1)/(m+1).                               (ALG2)
```

For a binary Leavitt cell at least one of the two diagonal inverse defects
and the completeness defect is at least `1/3`.  The estimate is independent
of `d`, `rank(p)` and `rank(p)/d`; in particular it remains `1/3` on a
rank-one corner in matrices of growing dimension.  The off-diagonal
relations `t_i s_j=0`, `i!=j`, are not used.

Equivalently, no nonzero projection in a norm matrix corona can carry an
exact `m`-ary Leavitt family.  Lift the projection and the finitely many
corner elements coordinatewise, compress to the lifted nonzero corners, and
apply `(ALG1)` on a subsequence.  This gives a quantitative coordinate proof
of the proper-infiniteness obstruction rather than an appeal to abstract
stable finiteness.

