---
rg: 2
id: agent-aggregate-escape-finite-packet-actor-no-go-proof
kind: route
title: Induce a packet representation around the finite automorphism image
target: agent-aggregate-escape-finite-packet-actor-no-go
requires:
  - agent-aggregate-escape-rfd-support-orientation-firewall
---

Let `H=alpha(L)`.  On

```text
W=direct_sum_(h in H) V_h,             V_h=V,
```

define, with one fixed consistent left/right convention,

```text
rho(f)|_(V_h)=sigma(alpha_(h^(-1))(f)).                (1)
```

For `k in H`, let `U_k` send `V_h` identically onto `V_(kh)`.  A direct
index change gives

```text
U_k rho(f) U_k^*=rho(alpha_k(f)),
U_k U_l=U_(kl).                                        (2)
```

Thus `(rho,U)` represents `F semidirect H`.  Compose `U` with
`alpha:L->H` to represent `F semidirect L`.  The summand `V_1` carries
`sigma`, proving the extension assertion.

If the actor fixes `K` and permutes the forbidden menu, conjugation by the
`U_k` permutes the nonnegative numbers `||T e_j||_2^2`.  A positive value in
the original summand remains positive in the orbit sum.  Normalization may
divide it by at most `|H|`, a fixed packet-dependent constant, but cannot
make it zero.  Since the representation is exact, this contradicts the
`E=0` instance of `(ACO4)`.
