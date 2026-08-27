---
rg: 2
id: aggregate-range-idempotence-replaces-gram-bookkeeping
kind: claim
title: One aggregate range idempotence defect controls all incoming branch Gram energy
distinct_from:
  partial-isometry-gram-is-range-overlap: that identifies one cross-Gram term with one pair of final projections; this theorem sums all pairs and packages the entire target penalty into one aggregate operator.
  gram-branching-capacity-with-overlap: that accepts pairwise Gram energy as input; this theorem gives a cheaper sufficient certificate for that input.
---

Let `(M,tau)` be a finite tracial von Neumann algebra and let
`T_1,...,T_N` be partial isometries.  Write

```text
F_a = T_a T_a^*,
F   = sum_a F_a,
s   = sum_a tau(F_a),
o   = sum_(a!=b) ||T_a^* T_b||_2^2.
```

Then the full ordered-pair Gram penalty is exactly the trace idempotence defect
of the aggregate range operator:

```text
o = tau(F^2-F).                                         (ARI1)
```

Consequently

```text
o <= ||F^2-F||_2.                                      (ARI2)
```

More generally, for a target projection `P` and total wrong-target leakage

```text
l = sum_a ||(1-P)T_a||_2^2,
```

one has

```text
s-l = tau(PF),
(s-l)^2 <= tau(P) tau(F^2).                            (ARI3)
```

Thus a branch-capacity proof never needs to estimate `N(N-1)` cross-Gram
terms separately.  It is enough to show that the single positive aggregate
`F=sum_a T_aT_a^*` is asymptotically idempotent.  In particular,

```text
l = O(delta^c),
||F^2-F||_2 = O(delta^c)
```

imply the same `O(delta^c)` capacity error required by
`gram-branching-capacity-with-overlap`.

This is useful for compiler-style atlas searches because exact branch packets
often identify a **sum** of ranges as one named projection even when no
convenient pairwise description exists.  The existing Pauli split is the model
example: its two outgoing ranges sum exactly to `U^*QU`, so their aggregate
idempotence is automatic.
