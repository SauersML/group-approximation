---
rg: 2
id: kt-full-actor-cocycle-loop-wall-proof
kind: route
title: Conjugate the canonical actor by the root lamp and evaluate every cocycle holonomy
target: kt-full-actor-cocycle-loops-admit-exact-wreath-wall
requires:
  - kun-thom-nonsofic-wreath
  - kt-ab-normalizer-row-forces-wall-gauge-propagation
---

Conjugation by the fixed unitary `v` makes `rho_0` a representation whenever
`rho_1` is one.  For `gamma in Gamma`, actor covariance fixes the root site,
so `u_gamma v u_gamma^*=v`; hence `(KCL2)` agrees on `Gamma`.  If `g!=1`,
the word `v u_g v` has nonidentity actor grade `g`, so its group trace is
zero.  At the identity it is `v^2=1`.  Thus both actor characters are
canonical.

For `h Gamma!=Gamma`,

```text
rho_0(h)rho_1(h)^*=v u_h v u_h^*
                  =a_Gamma a_(h Gamma).                 (KCP1)
```

The two binary lamps are distinct, so their product is a nonidentity element
of the lamp base and has group trace zero.  Therefore

```text
||rho_0(h)-rho_1(h)||_2^2
 =2-2 Re tau(rho_0(h)rho_1(h)^*)=2,                     (KCP2)
```

which proves `(KCL3)`.

For the loop audit put

```text
theta_g(x)=rho_1(g)^*x rho_1(g).
```

Direct multiplication gives the right nonabelian cocycle identity

```text
z_(gk)=theta_k(z_g)z_k,             z_gamma=1
                                      for gamma in Gamma. (KCP3)
```

In particular the cyclic relation contributes only

```text
theta_C^2(z_C) theta_C(z_C) z_C=1.                       (KCP4)
```

More generally, if `g_1...g_m=1` is any Steinberg or actor relator, then

```text
theta_(g_2...g_m)(z_(g_1))
 theta_(g_3...g_m)(z_(g_2)) ...
 theta_(g_m)(z_(g_(m-1))) z_(g_m)=1.                    (KCP5)
```

The coboundary `(KCL4)` satisfies `(KCP4)--(KCP5)` identically while
`(KCP2)` stays maximal.  Hence these closed products carry no positive
tracial energy by themselves.  Any inequality contradicting this exact
model must invoke an additional hypothesis absent from arbitrary finite
tracial algebras; for the intended route that hypothesis can only be
matricial approximability/Connes embeddability.
