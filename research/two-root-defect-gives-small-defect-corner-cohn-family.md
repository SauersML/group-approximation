---
rg: 2
id: two-root-defect-gives-small-defect-corner-cohn-family
kind: claim
title: A nonzero root defect carries two Cohn pairs whose defects have total rank below the support's rank
distinct_from:
  rank-four-isometry-relations-give-corner-cuntz-family: that asks for an exact order-two Leavitt family, completeness included, in a corner of positive rank; this asks only for two approximate Cohn pairs supported in a nonzero element, with total defect rank below that element's rank, which the exact family implies.
  corner-cohn-defects-bound-rank-in-rank-ultraproducts: that is the established inequality showing such data cannot exist; this is the open construction from a nonzero root defect, which the inequality turns into the rank gate.
artifacts:
  - research/artifacts/rank-four-completeness-check-2026-09-12.md
  - research/artifacts/rank-four-associativity-gate-plans-2026-09-12.md
---

**OPEN.** Let `K` be a finite field of characteristic `p`, `R = L_K(1,2)`, `M` a rank ultraproduct
over a field of characteristic `p`, and `sigma : EL_3(R) -> M^x` a homomorphism. Put
`N_ab = sigma(x_ab(1)) - 1`. Suppose `N_12^2 != 0` or `N_23 N_12 != 0`. Then there are an `x in M`
with `rk(x) > 0`, elements `S_0, S_1 in xM`, and `T_0, T_1 in M` such that

```text
sum over i, j in {0,1} of rk(delta_ij x - T_i S_j)  <  rk(x) .
```

**Status of the conclusion.** By `corner-cohn-defects-bound-rank-in-rank-ultraproducts` the
conclusion can never hold. So this claim is equivalent to `N_12^2 = 0` and `N_23 N_12 = 0` for the
models in scope, and its whole content is the construction, which would be the proof. The same is
true of the exact node `rank-four-isometry-relations-give-corner-cuntz-family`. This node asks for
strictly less:
- no completeness;
- no idempotent;
- no exact relations;
- no condition on where the `T_i` live.

In characteristic two `N_12^2 = 0` holds automatically, so only `D = N_23 N_12 != 0` matters.

## Attempts

- **Implied by the exact plan (w4-r4-complete, 2026-09-12).** An order-two Leavitt family in `eMe`
  with `rk(e) > 0` is zero-defect data with `x = e`. So
  `rank-four-isometry-relations-give-corner-cuntz-family` implies this claim, and its check (ii),
  completeness, is not needed.
- **Choice of support.** Take `x = D`, or the left projection `e` of `D`
  (`eM = DM`, `rk(e) = rk(D)`; `M` is von Neumann regular). Then `rk(x) > 0` is automatic, which
  settles check (iii) of the exact plan. The construction must put `S_0, S_1` in `DM`.
- **Root products do not have the right support as they stand.** Put `A_i = n_12(t_i)` and
  `B_j = n_23(s_j)`. The isometry commutator relations give `A_i B_j = delta_ij n_13(1)` plus
  reversed-order terms (`leavitt-isometry-commutators-constrain-el3-rank-models`). But in the
  natural model `n_ab(r) = rho(r) E_ab` the element `B_j` does not lie in `n_13(1) M`, and in any
  case the natural model has `D = 0`. So the supports have to be re-chosen, for example by
  multiplying on the left by `D`, and the budget then has to be controlled. No construction yet.
- **Where it stops.** Open. Theorem 1 of the artifact is the whole contradiction mechanism, so all of
  the difficulty sits in the rank budget.
