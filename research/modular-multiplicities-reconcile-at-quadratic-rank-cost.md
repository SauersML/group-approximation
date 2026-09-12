---
rg: 2
id: modular-multiplicities-reconcile-at-quadratic-rank-cost
kind: claim
title: Arbitrary modular multiplicities reconcile by an exact quadratic-rank change
distinct_from:
  modular-strata-have-linear-coordinates-and-rank-splits: that assumes matching generator multiplicities; this removes that hypothesis by an exact small-rank change preserving the common central involution relation.
  iwahori-torsion-multiplicity-stratum-reconciliation: that includes an Iwahori endpoint discussion and a proposed defect-controlled strengthening; this proves explicit rank and HS bounds for two supplied vertex endpoints, without constructing a compatible endpoint from its defect.
  dilution-obstructs-flat-quadratic-iwahori-repair: that excludes uniformly flat repair directions on dilute incompatible inputs; this allows concentrated changes and uses a supplied comparison representation.
artifacts:
  - research/artifacts/modular-multiplicity-rank-reconciliation-2026-09-08.md
---

Let `rho,rho':SL_2(Z)=C_4 *_(C_2) C_6 -> U(d)` be any two exact
representations on the same space, with generator matrices `S,B` and
`S',B'`. No agreement of their generator or central multiplicities is
assumed. Put

```text
delta=max(||S-S'||_2,||B-B'||_2),
K=1+2sqrt(3),        C=pi(1+pi)/sqrt(3),
```

using normalized Schatten norms. There is an exact representation
`rho_tilde` with the same `S`- and `B`-eigenvalue multiplicities as
`rho'` such that

```text
rank(rho_tilde(s)-rho(s))/d <= 2 delta^2,
rank(rho_tilde(b)-rho(b))/d <= 3 delta^2,
max_g ||rho_tilde(g)-rho(g)||_2 <= 2sqrt(3)delta,
max_g ||rho_tilde(g)-rho'(g)||_2 <= K delta,              (MMR1)
```

where `g` ranges over `{s,b}`. In particular the common relation
`rho_tilde(s)^2=rho_tilde(b)^3` holds exactly throughout the
construction. No padding is needed. The natural modular chart at
`rho_tilde` reaches `rho'` with parameter tuple of normalized HS norm
at most `CK delta`.

There is also an exact operator/rank factorization for these arbitrary
endpoints. For every `theta>0` there is an exact representation
`rho_lo` such that

```text
max_g ||rho_lo(g)-rho(g)||_op <= 4theta,
max_g rank(rho_lo(g)-rho'(g))/d
    <= 3delta^2 + 4C^2 K^2 delta^2/theta^2.              (MMR2)
```

The same constants work for two vertices with maximum tuple norms.
If the second vertex pair is a supplied compatible Iwahori pair, then
`(MMR1)` moves the first pair into its multiplicity stratum at HS
cost `O(delta)` and changes each fixed-word compatibility residual by
`O(delta)`. This proves qualitative multiplicity reconciliation as
`delta->0`. It supplies neither a compatible endpoint from a small
defect nor a bound `delta=O(defect)`, and does not repair the
invalidated normalized-HS Newton argument. The intermediate pairs
need not be Iwahori compatible. Rank bounds are generatorwise and
assert no common reducing summand for the full representation.
