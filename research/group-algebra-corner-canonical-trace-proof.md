---
rg: 2
id: group-algebra-corner-canonical-trace-proof
kind: route
title: Normalize the faithful coefficient trace on a nonzero projection corner
target: group-algebra-corners-exclude-traceless-leavitt-inputs
requires: []
---

Let `tau_G:C[G]->C` take the coefficient of the identity and put

```text
Tau_n([a_ij])=sum_i tau_G(a_ii).                            (GCT3)
```

This is a trace.  It is positive and faithful on the algebraic group ring:
if `X=[x_ij]`, then

```text
Tau_n(X^*X)=sum_(i,j) tau_G(x_ij^*x_ij)
            =sum_(i,j) sum_(g in G) |(x_ij)_g|^2.           (GCT4)
```

Hence `(GCT4)` is positive for `X!=0`.  In particular `(GCT1)` gives
`Tau_n(p)>0`, and

```text
tau_p(x)=Tau_n(x)/Tau_n(p),          x in pM_n(C[G])p,       (GCT5)
```

is a tracial state with `tau_p(p)=1`.

If `Phi:B->pM_n(C[G])p` is a star homomorphism with `Phi(1_B)=p`, then
`tau_p o Phi` is a tracial state on `B`.  Thus no traceless unital star
algebra can admit such a map.

For `(GCT2)` the contradiction is visible without any general terminology.
If `sigma` were a tracial state, then

```text
sigma(s_i s_i^*)=sigma(s_i^*s_i)=sigma(1)=1,
```

while the completeness row gives

```text
1=sigma(1)=sigma(s_0s_0^*)+sigma(s_1s_1^*)=2.
```

Therefore the complex binary Leavitt/Cuntz star algebra is traceless and the
first part excludes its unital occurrence in the corner.  For a
characteristic-two unital algebra, a unital ring map would instead give

```text
0=Phi(2*1)=2p,
```

impossible because `p!=0` in the complex vector space `M_n(C[G])`.
