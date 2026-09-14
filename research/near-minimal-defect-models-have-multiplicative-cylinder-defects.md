---
rg: 2
id: near-minimal-defect-models-have-multiplicative-cylinder-defects
kind: claim
title: A fixed-point-free Leavitt rank model whose defect is near the infimum has multiplicative defects on disjoint cylinders
distinct_from:
  nested-two-root-defect-pieces-decay-geometrically-both-ways: that bounds the per-step ratio of the nested defect ranks between the gap and one half for every model; this shows that at near-minimal defect the ratio is pinned to the defect itself, so products of disjoint cylinder defects have the ranks of independent tensor factors.
artifacts:
  - research/artifacts/two-root-defect-descent-gap-2026-09-12.md
---

**ESTABLISHED** (route `near-minimal-defect-multiplicativity-proof`; artifact Section 4;
independent re-derivation requested from `w4-vf-gate`).

**Statement.**
* **Setting.** `sigma` is a nontrivial fixed-point-free characteristic-two rank model of
  `R^x = L_(F_2)(1,2)^x`, with `delta = rk(D_1000) <= (1+eps) c_*`, where `c_*` is the infimum of
  the normalized defect over such models.
* **Conclusion.** For pairwise disjoint proper cylinders with proper union,

  ```text
  | rk(D_(A_1) ... D_(A_(k+1))) - delta · rk(D_(A_1) ... D_(A_k)) |  <=  eps delta ,
  | rk(D_(A_1) ... D_(A_k)) - delta^k |  <=  2 eps delta .
  ```

**Why it matters.** The two restrictions a commuting defect offers are the range corner and the
kernel corner. At a near-minimal model both give models whose normalized defect is within `O(eps)`
of `delta`. So:
* no iterate of these restrictions lowers the defect by a fixed factor;
* the numbers are exactly those of a tensor product of independent factors;
* a proof of the gate by minimal counterexample has to rule out this tensor-like pattern using the
  Leavitt relations.
