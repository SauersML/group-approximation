---
rg: 2
id: invariant-free-near-state-is-amenable-regular-cover
kind: claim
title: An invariant free near-state is an amenable-trace cover of the reduced group algebra
distinct_from:
  normal-state-free-near-representation-forces-factorization: that uses normality to make the near representation genuine on a support projection; this works for arbitrary invariant states and keeps the singular defect in the trace-kernel quotient.
  hyperlinear-near-representation-criterion: that characterizes hyperlinearity by existence of a near representation; this identifies the exact C-star extension carried by every state-form witness.
---

Let `G` be a group, let `pi:G -> U(H)` be a state-form near representation,
and let `phi` be a state on `B(H)` such that

```text
phi(pi(g) T pi(g)^*)=phi(T)                       for all g,T,
phi((pi(gh)-pi(g)pi(h))^*(pi(gh)-pi(g)pi(h)))=0   for all g,h,
phi(pi(g))=0                                      for g != 1.      (ANR1)
```

Put `A=C^*(pi(G))` and `tau=phi|_A`. Then:

1. `tau` is a tracial state on `A`, and in fact an amenable trace, witnessed
   by the same state `phi` on `B(H)`;
2. the tracial null ideal

   ```text
   I_tau={a in A : tau(a^*a)=0}
   ```

   is a closed two-sided ideal containing every multiplicative defect
   `pi(gh)-pi(g)pi(h)`;
3. the quotient is canonically trace-preservingly isomorphic to the reduced
   group C-star algebra,

   ```text
   (A/I_tau, bar tau) ~= (C^*_r(G), tau_G).              (ANR2)
   ```

Consequently every state-form hyperlinearity witness is an amenable-trace
C-star cover of the regular representation; all failure of genuine
multiplicativity is confined to the trace-kernel ideal.

If `phi` is purely singular on `B(H)`, then it annihilates `K(H)` and factors
through the Calkin algebra. Thus the singular witness required by the binary
Leavitt fork is more specifically a Calkin-supported amenable-trace cover of
`C^*_r(G)` whose trace-kernel quotient is regular.
