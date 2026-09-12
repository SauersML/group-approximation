---
rg: 2
id: corner-cohn-defects-bound-rank-in-rank-ultraproducts
kind: claim
title: In a rank ultraproduct two Cohn pairs supported in x bound rk(x) by the total rank of their defects
distinct_from:
  leavitt-algebra-has-no-unital-rank-model: that forbids a unital homomorphism of the Leavitt algebra, using completeness, simplicity and direct finiteness of the whole ultraproduct; this bounds the rank of any element carrying two approximate Cohn pairs, with no completeness, no idempotent and no simplicity.
  anti-central-rank-models-kill-ternary-corner-witnesses: that applies a positive rank function to witnesses of the ternary corner equation; this is the general two-pair defect inequality in any rank ultraproduct.
artifacts:
  - research/artifacts/rank-four-completeness-check-2026-09-12.md
---

**ESTABLISHED** by `corner-cohn-defects-bound-rank-proof`. Elementary; no priority is claimed.

Let `F` be any field and `M = prod_omega M_(n_k)(F) / d_omega` a rank ultraproduct with normalized
rank `rk`. Let `x in M`, `S_0, S_1 in xM` and `T_0, T_1 in M`. Then

```text
rk(x)  <=  sum over i, j in {0,1} of  rk(delta_ij x - T_i S_j) .
```

The same bound holds with `T_0, T_1 in Mx` and `S_0, S_1` arbitrary, and for square matrices over
`F` with normalized rank.

**Corollary.** If `S_j in xM` and `T_i S_j = delta_ij x` exactly, then `x = 0`. So a corner two-pair
Cohn family (`S_j, T_i in eMe`, `T_i S_j = delta_ij e`) forces `e = 0`. The completeness relation
`S_0 T_0 + S_1 T_1 = e` is never needed.

**Consequence for the rank gate.** In `rank-four-isometry-relations-give-corner-cuntz-family`:
- check (ii), completeness, is dispensable;
- check (i) relaxes to a rank budget;
- check (iii) is automatic when `x` is the two-root defect `D = N_23 N_12`, or its left projection.

See `two-root-defect-gives-small-defect-corner-cohn-family`, the route
`leavitt-el3-triviality-via-cohn-rank-inequality`, and Section 1 of the artifact.
