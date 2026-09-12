---
rg: 2
id: finite-verifier-type-positive-loss-proof
kind: route
title: Sum the positive verifier losses and use faithfulness of the decoded tracial GNS quotient
target: finite-tailored-checks-reduce-to-typewise-positive-loss-gadgets
requires:
  - tailored-gap-checks-form-common-complete-nemesis-library
---

By `(TCN1)` from
`tailored-gap-checks-form-common-complete-nemesis-library`, every CE strategy
`S` obeys

```text
sum_(c in C) beta_c tau_S(L_c)>=1/2.                    (FVP1)
```

Partitioning the finite sum gives the first inequality in `(FVT2)`, and the
maximum of `|T|` nonnegative numbers is at least their average, giving the
second.

If one marked canonical CE base type extended every `E_t`, the common base
decoder would give one strategy `S`; `(FVT3)` for every `t` would make the
left side of `(FVP1)` zero, a contradiction.  The stipulated common perfect
infinite completion realizes all gadgets simultaneously, so the nemesis
family is common-complete.

Finally each `L_c` is a projection, hence positive.  Since `beta_c>0`,
`epsilon_t(S)=0` implies `tau_S(L_c)=0` term by term.  In the faithful GNS
quotient,

```text
||L_c||_(2,tau)^2=tau_S(L_c^*L_c)=tau_S(L_c)=0,
```

so `L_c=0`.  This proves `(FVT4)`.

The last paragraph of the claim is not an additional inference: it records
the hypothesis of `(TCO1)--(TCO4)` in
`transitive-controller-orbit-common-twist-preserves-zero-lcu`.  Syntactic
membership in one verifier type supplies no group action satisfying `(TCO4)`.
