---
rg: 2
id: infinite-index-coset-payload-erasure-proof
kind: route
title: Sum equal-trace orthogonal carriers and compute the quasi-regular coefficient
target: infinite-index-factor-induction-kills-every-coset-payload
requires:
  - infinite-index-canonical-subgroup-corner-is-impossible
---

Trace invariance and covariance in `(IIP1)` make

```text
tau(p_x)=c
```

independent of `x`.  The sum of any `N` distinct carriers is a projection,
so finiteness of the trace gives `Nc<=1`.  Since `I` is infinite, `c=0`.
Faithfulness gives `p_x=0`; for a nonfaithful state,
`||p_x||_(2,tau)^2=tau(p_x)=0`, so the GNS representation kills it.  This
proves `(IIP2)` and applies to the usual direct-sum induced representation,
whose base factor is stored in `p_H M p_H`.

If `m` is an invariant mean on `ell^infinity(I)`, transitivity again makes
all singleton values equal.  Finite additivity on arbitrarily many distinct
singletons forces

```text
m(1_{x})=0.                                           (IIE1)
```

Hence the projection `1_{x}` is zero in the GNS representation of `m`, and
tensoring it with any finite factor does not change that conclusion.

Finally `(IIP3)` is the indicator of `H`.  A coefficient of a group
representation defines a tracial state on the group algebra exactly when it
is conjugation invariant.  The indicator `1_H` is conjugation invariant
exactly when `H` is normal.  If it is normal, the quasi-regular action is the
left regular action of `Lambda/H`; its GNS algebra is `L(Lambda/H)`, with no
copy of the input factor.  A commensurated but nonnormal Hecke pair therefore
does not evade the character requirement.
