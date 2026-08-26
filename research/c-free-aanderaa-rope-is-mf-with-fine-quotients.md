---
rg: 2
id: c-free-aanderaa-rope-is-mf-with-fine-quotients
kind: claim
title: The C-free modular-machine rope is MF, its insertion subgroup is closed, and its finite quotients refine the evaluation map
distinct_from:
  benign-witness-finite-quotients-refine-the-fold: that is the profinite hole of the benign-witness rope; this is the corresponding hole of the modular-machine rope, whose engine is already MF.
  boone-base-has-corona-inner-instruction-automorphisms: that is the Turing-engine corona hole; the modular engine needs no such statement.
---

With the notation of [[product-commuting-aanderaa-cohen-compiler]], show
for every modular machine `M` (uniformly) that

```text
(a) Gamma_a is operator-MF;
(b) A_+ = < U, d, b, p > is closed in the finite-quotient topology of Gamma_a;
(c) for every finite-index normal subgroup C' of C there is a finite quotient
    of Gamma_a whose kernel meets A_+ inside tau^-1(C').           (CF1)
```

Together with [[product-commuting-aanderaa-cohen-compiler]] and
[[twisted-edge-over-amalgamated-product-base-is-mf]] this proves that the
compiler is MF-safe and closes
[[mf-recognition-finite-presentations-is-pi2-complete]].

## Attempts

*Engine.*  `K_M` is regularly MF by [[modular-machine-boone-group-is-mf]];
in fact, in the enlarged base `E = (BS(1,m) x BS(1,m)) *_(Z^2) (Z^2 x <t>)`
(letters `mu, nu` commuting with `t`) every machine twist is inner, so `K_M`
sits in a multiple central HNN extension of the residually finite amenable
amalgam `E`.

*The `p` layer.*  `H_2^0 = P_0 *_T K_M` with `P_0 = Lambda *_psi`, `Lambda =
T * F(b) * <d>` free, and `psi : t_alpha -> t_alpha w_alpha(b) d` the
restriction of an automorphism of `Lambda`.  `P_0` is residually finite: for
finite quotients `Q''` of `F(b,d)` and any finite group `Q'''`, the
assignment `t_alpha -> ((w_alpha(b) d, X_alpha), 1)` into `(Q'' x Q''') x
Q''` synchronizes the edge kernels and separates `Lambda`.  The amalgam `P_0
*_T K_M` over the infinite-rank free group `T = <<t>>_K` is where the attack
stops: the restrictions to `T` of the concrete realizations of `P_0` (finite
quotients) and of `K_M` (finite quotients of `E`, in which `t(r,s)` is
periodic in `(r,s)`) are not conjugate, and an abstract realization of `K_M`
gives no control on `T`.

*The `a_i` layer.*  `psi_i = Ad(x^-i mu) o beta_i` where `beta_i` is the
automorphism of the enlarged `p`-group fixing `E, b, C`, sending `d -> b_i
d` and `p -> (x^-i mu)^-1 p (x^-i mu)`; so the `a_i` layer embeds in a
central HNN extension of the mapping torus by the free group on the
`beta_i`.  The transvection part `F(b,d) x| F(beta)` is residually finite
(HNN of `F(b) x F(beta)` between a graph and a factor).

*(b), (c).*  Not yet examined; both concern the finite-quotient topology of
`Gamma_a` on `A_+`, whose `F(b)`-coordinate is free and whose `U`-coordinate
is the halting subgroup.
