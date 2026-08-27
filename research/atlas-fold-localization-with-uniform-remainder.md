---
rg: 2
id: atlas-fold-localization-with-uniform-remainder
kind: claim
title: Low-defect atlas microstates localize at the classical fold with a uniform quadratic remainder
distinct_from:
  atlas-boundary-tangent-covariance-coercivity: that is the established first-order inequality AT the fold; this is the missing global input that says there is nowhere else to be, and it is what turns a local constant into the dimension-free implication.
  atlas-charts-overlap-trivially: that is a statement about the two chart images intersecting; this is a metric statement about the position of a low-defect chart unitary relative to one distinguished point.
artifacts:
  - notes/ATLAS_BOUNDARY_RANK_THREE_EXACT_AUDIT.md
  - research/artifacts/atlas-asc-tangent-exact-2026-08-19.md
---

OPEN.  Let `S_0` be the first-boundary packet together with the interior
separator `c_19243 = [p1_12, q_19243]`.  Ask: is there a function
`delta(eps) -> 0` such that for every multiplicity `k` and every
`U in U(20160k)` with

```text
max_(s in S_0) ||pi_U(s)-1||_2 <= eps,
```

there is a gauge element `V` of the commutant of `lambda (x) I_k` on each
side with

```text
|| V_1 U V_2 - 1 ||_2 <= delta(eps),
```

and with the second-order remainders of the boundary and covariance forms
bounded by `O(delta^3)` uniformly in `k`?

**Why the interior word has to be in `S_0`.**  For the boundary packet alone
the answer is no: `ATLAS_BOUNDARY_RANK_THREE_EXACT_AUDIT` builds
`E = M semidirect A_8` with `dim_F2 M = 155` in which all 234 first-boundary
words vanish exactly, both chart restrictions are regular, and the two `H`
copies still disagree.  That is a far component with zero boundary defect.
The same audit shows one interior centrality condition attached to collision
word `19243` kills the entire affine family in its order-zero quotient, which
is why the localization is asked for `S_0` and not for the boundary alone.

**What it would buy.**  Together with
`atlas-boundary-tangent-covariance-coercivity` -- whose constant `1/14` is
already independent of `k` -- it gives the open claim
`atlas-two-s3-covariance-collapse`: localization puts every low-defect model
in the regime where the quadratic forms govern, and the dimension-free
constant then forces `a^2+b^2 -> 0` against the proved floor `1/40`.

This is item 5 of the attempt list of `atlas-two-s3-covariance-collapse`
stated as its own hole, now that the coercivity half of it is established.
