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

First split each ordered product into closest-half consecutive subproducts.
Associativity proves every row `(BAT3a)`, and products of isometries remain
isometries.  The resulting multiplication depth is `ceil(log_2 m)` and its
root is exactly `(BAT1)` (including the scalar sign link).

Substitution into `(BAT2)` then proves `(BAT3)`.  If
`I=I_0 disjoint_union I_1`, separating the two sums in `(BAT2)` proves
`(BAT4)`.  A closest-half split of an integer `q>=2` has child ratios

```text
floor(q/2)/q, ceil(q/2)/q in [1/3,2/3],
```

and iterating closest-half splits gives addition depth `ceil(log_2 N)`.
Taking `I=S_m` proves `(BAT5)`.  Finally, exact multiplication, sign-link,
and addition rows identify the root with the standard polynomial under every
evaluation; at `m=2n` it vanishes on `M_n(C)`, while `(BAT3)` verifies
`(BAT6)` in the Fock model.
