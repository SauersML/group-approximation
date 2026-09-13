---
rg: 2
id: leavitt-unit-algebra-absorbs-an-induced-projective
kind: claim
title: A free module over F_2 of the binary Leavitt unit group absorbs a nonzero module induced from a finite subgroup
refuted_by:
  - finite-subgroup-induced-absorption-conserves-entropy
  - leavitt-unit-group-surjunctive
distinct_from:
  leavitt-unit-group-algebra-not-directly-finite: that asks for a one-sided inverse in F_2[U] itself; this asks for one in some matrix ring M_n(F_2[U]) whose defect module is induced from finite subgroups. Neither statement implies the other as written, and this one is refuted for every group.
  leavitt-module-dual-actions-are-self-squares-off-bernoulli: that is exact doubling over U through Leavitt modules, which never gives a Bernoulli factor; this was absorption inside the group algebra with a co-induced absorbed factor.
---

**REFUTED** (landed open at d2a8ad5ce4 and refuted by this lane the same day).
`finite-subgroup-induced-absorption-conserves-entropy` shows that no free `F_p[G]`-module, over any group,
absorbs a nonzero module induced from finite subgroups. The additive lifted p-adic trace of
`lifted-trace-detects-finite-subgroup-projectives` takes the value `sum dim(Q_i)/|F_i| > 0` on the summand
and must take the value `0`. Consequence 3 of that node already records the defect form of this exclusion.
This lane missed it before landing.

**The statement, kept for the record.** Let `L = L_(F_2)(1,2)` and `U = L^x`. There are `n >= 1`, finite
subgroups `F_i <= U` and finite-dimensional `F_2[F_i]`-modules `Q_i`, not all zero, with
`F_2[U]^n ≅ F_2[U]^n ⊕ ⊕_i F_2[U] ⊗_(F_2[F_i]) Q_i`. The smallest shape was `c` of order 3 and the summand
`F_2[U](c + c²)`, with `rho = 2/3`.

## Attempts

- **Quotient.** In `L` every nonzero idempotent `e` gives `L ≅ L ⊕ Le`. That is exactly why `L` has no
  lifted trace: the trace lives on `F_2[U]` and dies on the quotient.
- **Mod-2 filter.** For odd `|F_i|`, `rho = 0` in `F_2` is necessary, and `rho = 2/3` passes it. The p-adic lift
  of the same trace is `rho` itself, which kills the target outright. The mod-`p` shadow of a trace is not the
  trace.
- **Dead route.** `leavitt-induced-absorption-gives-bernoulli-collapse`.
