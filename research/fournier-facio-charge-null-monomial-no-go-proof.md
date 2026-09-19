---
rg: 2
id: fournier-facio-charge-null-monomial-no-go-proof
kind: route
title: Pass invariance through the state null ideal and remove all charge-null mixing
target: fournier-facio-charge-null-monomial-perturbations-impossible
requires:
  - fournier-facio-monomial-near-witness-impossible
---

Write

```text
N_mu={K in B(ell^2(X)): phi_mu(K^*K)=0}.              (FCNP1)
```

By Cauchy--Schwarz for the state, `N_mu` is a linear left ideal.  Put
`K_g=pi(g)-M_g`, so `(FCN2)` says `K_g in N_mu`.

First transfer invariance.  For arbitrary `T`, expand

```text
pi(g)^*T pi(g)-M_g^*T M_g
 =K_g^*T M_g+M_g^*T K_g+K_g^*T K_g.                  (FCNP2)
```

Each term has zero `phi_mu` value by Cauchy--Schwarz and
`phi_mu(K_g^*K_g)=0`.  Invariance under `Ad(pi(g))` therefore implies
invariance under `Ad(M_g)`.  Restricting to diagonal projections shows that
the permutation `alpha_g` underlying `M_g` preserves `mu`.

This last conclusion makes the null ideal stable under right multiplication
by `M_g`: for `K in N_mu`,

```text
phi_mu((K M_g)^*(K M_g))
 =phi_mu(M_g^*K^*K M_g)=phi_mu(K^*K)=0.              (FCNP3)
```

Now put

```text
d_pi(g,h)=pi(gh)-pi(g)pi(h),
d_M(g,h)=M_(gh)-M_g M_h.
```

Direct expansion expresses `d_M-d_pi` as a sum of

```text
K_(gh),       K_g M_h,       M_g K_h,       K_g K_h. (FCNP4)
```

Every term lies in `N_mu`: use `(FCNP3)` for `K_gM_h` and the left-ideal
property for the other three.  The near-representation identity gives
`d_pi(g,h) in N_mu`, hence `d_M(g,h) in N_mu`.  Thus every multiplication
row holds for `M` in the same charged sense.

Finally `(FCN2)` and finitely additive Markov imply `(FCN3)`.  All
pointwise essential-freeness tests for `pi(g)` consequently transfer to
`M_g`.  The monomial family is therefore an essentially free amenable near
representation of `G`, contradicting
`fournier-facio-monomial-near-witness-impossible`.
