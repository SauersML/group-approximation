---
rg: 2
id: subshift-elementary-group-lef-growth-tracks-complexity
kind: claim
title: The LEF growth of EL_3(LC(X,F_q)⋊Z)/Z is controlled by the complexity function of the minimal subshift X
---

**OPEN.** For `S_X = EL_3(LC(X,F_q)⋊Z)/Z`, let `L_X(r)` be the least order of a finite group `F` admitting a map
from the `r`-ball of `S_X` (for `σ_X`) that is injective and multiplicative on the ball (Bradford-style LEF
growth). Let `p_X(n) = |L_n(X)|` be the complexity function. Is there `C` such that
`p_X(r/C) ≲ log L_X(r) ≲ p_X(Cr)^C`, uniformly in the minimal subshift `X`? That would make the zero-entropy /
positive-entropy distinction, and polynomial complexity scales, visible in the group.

## Attempts

- **Upper bound (sketch, lane un-open-5).** The LEF models of `minimal-subshift-algebra-is-simple-lef-ring`
  item 3 use periodic words whose cyclic windows of length `2k+1` are exactly `L_(2k+1)(X)`. Such a cyclic word
  is a closed walk in the Rauzy graph of order `~2k` visiting every vertex. Its length `N_k` satisfies
  `p_X(2k+1) ≤ N_k ≤ p_X(2k+1)^2`. Words of length `r` in `σ_X` are matrices whose entries have radius `O(r)`
  (propagation) and `u`-degree `O(r)`. So an exact model at radius `r` needs `k = O(r)`, and embeds in
  `GL_(3N_k)(F_q)`, which gives `log L_X(r) ≤ 9 N_(Cr)^2 log q`. The constant bookkeeping has not been checked.
- **Lower bound, where it dies.** The trivial bound `L_X(r) ≥ |B(r)| ≥ c^r` does not see `p_X`. Group-level
  local models of `EL_3(R_X)` need not come from ring models. A lower bound of the form `exp(p_X(r/C))` would
  need a rounding principle: local group models of `EL_3` induce local ring models on the root subgroups
  `e_12(LC_m(X))`, forcing rank `≥ p_X(m)`. That is an instance of the open converse
  `lef-el-groups-force-exactly-matricial-simple-ring`.
- **Firewall.** Approximation type (LEF, (T), simplicity) is constant in `X`. Only quantitative or
  computability invariants can separate the `S_X`. See `subshift-elementary-group-word-problem-equals-language`
  for the computability side.
