---
rg: 2
id: one-seed-character-expansion-proof
kind: route
title: Put half the mark in nonzero characters and apply the PVM expander ledger
target: one-pauli-seed-character-expansion
requires:
  - expander-pvm-transport-forces-dimension-or-mass-collapse
---

Fourier expansion and operator-valued Parseval give, for every actor color
`s`,

```text
E_a ||C_sU(a)C_s^*-U(g_s a)||_2^2
 =sum_x ||C_sP_xC_s^*-P_(g_s^(-*)x)||_2^2.                    (1)
```

Discarding the nonnegative `x=0` term shows that the PVM transport energy on
`Omega` is at most `eta_act^2`.  Put

```text
mu_1=sum_(x!=0) tr_d(P_x).
```

If `d<(2^n-1)/2`, `(EP3)` applied to the dual Schreier graph gives

```text
mu_1 <= eta_act^2/gamma.                                      (2)
```

It remains to charge the mark to `mu_1`.  On `PH`, the `-1` eigenspace of
`U(a_0)` is contained in the sum of the nontrivial character spaces.  Since
trace is invariant under conjugation and `||P||_2=sqrt(mu)`, `(OPS2)` gives

```text
2 |tr_d(P U(a_0))|
 =|tr_d(P(ZU(a_0)Z^*+U(a_0)))|
 <=sqrt(mu) eta_seed.                                         (3)
```

If `p_-` is the normalized trace of that `-1` eigenspace, then

```text
p_-=(mu-tr_d(PU(a_0)))/2
 >=mu/2-sqrt(mu)eta_seed/4.                                   (4)
```

Hence `mu_1>=p_-`.  Combine `(2)--(4)`:

```text
mu/2-sqrt(mu)eta_seed/4 <= eta_act^2/gamma.                   (5)
```

Using

```text
sqrt(mu)eta_seed/4 <= mu/4+eta_seed^2/16
```

in `(5)` proves `(OPS4)`.
