---
rg: 2
id: balanced-amitsur-isometric-tree-proof
kind: route
title: Normalize every partial Fock sum and split its leaf set in halves
target: balanced-amitsur-tree-has-bounded-isometric-gates
requires:
  - one-sided-amitsur-oracle-has-bounded-fock-model
---

Prefix incomparability in the required claim gives

```text
V_sigma^*V_tau=delta_(sigma,tau)I.
```

Substitution into `(BAT2)` proves `(BAT3)`.  If `I=I_0 disjoint_union I_1`,
separating the two sums in `(BAT2)` proves `(BAT4)`.  A closest-half split of
an integer `q>=2` has child ratios

```text
floor(q/2)/q, ceil(q/2)/q in [1/3,2/3],
```

and iterating closest-half splits gives depth `ceil(log_2 N)`.  Taking
`I=S_m` proves `(BAT5)`.  Finally, exact tree rows identify the root with the
standard polynomial under every evaluation; at `m=2n` it vanishes on
`M_n(C)`, while `(BAT3)` verifies `(BAT6)` in the Fock model.

