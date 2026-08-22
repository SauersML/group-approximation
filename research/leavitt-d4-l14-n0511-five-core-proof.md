---
rg: 2
id: leavitt-d4-l14-n0511-five-core-proof
kind: route
title: Substitute the five splitter partitions and identify their common periodic normal form
target: leavitt-d4-l14-n0511-five-branches-share-one-core
requires:
  - leavitt-d4-l14-n0511-branch-i-needs-nontrivial-carrier
---

The five substitutions in `(N5C1)` are the maximal noncrossing partitions
of the alternating word `a_3q_2d_3e_2f_3g_2t_3`.

In `H=k_1q_1d_2e_1f_2g_1t_2`, combine adjacent same-copy terms after each
branch substitution.  Branches I--V respectively use

```text
dft=a^-1,  dt=a^-1,  ft=a^-1,  t=a^-1,  t=a^-1,
```

and the complementary copy-one product is the identity.  Hence every case
gives `H=k_1a^-1_2`.

The copy-zero projection of the remaining carrier equation is
`kb=f^-1d^-1`.  In the five branches the right side is respectively
`ta,ta,ta,1,1`, while `at=1` in the last two cases, so `(N5C2)` follows.

Finally

```text
B0=i_0j_1k_2a^-1_3,       E6=t_0i_1j_2k_3.
```

For `B1`, branches I and II give `b^-1_0a^-1_1i_2j_3` directly.  Branch III
uses `ce=b^-1qe=b^-1`; branch IV uses
`ceg=b^-1qeg=b^-1`; branch V uses `cg=b^-1qg=b^-1`.
Substitution in `F=H^-1B0H^-1B1H^-1E6` proves `(N5C3)`.
The reduced-word conclusions follow immediately from `(N5C4)` and the
already proved `H=1` stratum.

