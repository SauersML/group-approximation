---
rg: 2
id: subshift-elementary-group-reduced-cstar-has-unique-trace
kind: claim
title: The reduced C*-algebra of EL_n(LC(X,F_2)⋊Z) has a unique tracial state
---

**ESTABLISHED (unreviewed; routine).** Let `X` be an infinite minimal subshift and `n ≥ 3`. Then
`C*_r(EL_n(LC(X,F_2) ⋊_T Z))` has exactly one tracial state, the canonical trace `τ(λ_s) = δ_{s,e}`. Over `F_q` the
same holds for `EL_n/Z`.

**Reason.**
- `G` is simple and infinite with property (T), so it is nonamenable, and its amenable radical is trivial.
- Every tracial state on `C*_r(G)` concentrates on the amenable radical (Breuillard–Kalantar–Kennedy–Ozawa, Theorem 4.1).

So `τ(λ_s) = 0` for every `s ≠ e`.

This is weaker than C*-simplicity, which is open: `subshift-elementary-groups-are-cstar-simple`.

Route: `subshift-elementary-group-reduced-cstar-has-unique-trace-proof`.
