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

*Re-based tower (2026-08-26).*  `Gamma_a` is also the HNN extension of
`Gamma_a' = < K_M * F(b,d), a_i | psi_i' >` (Cohen's `psi_i` with `p`
removed from the associated subgroups, still an isomorphism `F(t,x) *
F(b,d) -> F(t_i,x^m) * F(b_i d, b)`) by the single letter `p` over the
finite-rank free subgroups `< t, a_1, ..., a_(2n) > -> < t d, a_1, ...,
a_(2n) >`, basis to basis: conjugating `p t p^-1 = t d` by positive words
in the `a_i` reproduces every `p t_alpha p^-1 = t_alpha w_alpha(b) d`, so the
two presentations define the same group, and `Gamma_a' <= Gamma_a` by
Cohen's goodness of `< t, x, d, b >`.  Thus the whole `p`-layer is one
basis-to-basis edge over a rank-`(2n+1)` free subgroup, the same shape as
the Turing-engine edge of
[[boone-base-semidirect-product-is-hnn-over-free-subgroups]].

*Periodicity obstruction.*  No finite quotient of `Gamma_a` (or of `H_2^0`)
can synchronize the `p`-edge: if `xbar` has order `N` in a finite quotient
then `tbar_alpha = tbar_(alpha+N)`, and the `p`-relations force
`w_alpha(b) = w_(alpha+N)(b)` in the quotient for every `alpha`; the map
`alpha -> w_alpha(b)` is not `N`-periodic modulo any finite quotient of
`F(b)` in which the `b_i` survive (carries change all digits).  Hence
`H_2^0` is not residually finite, its finite quotients are small on `F(b)`,
and neither the twisted-edge theorems nor the synchronized-HNN theorem can
treat the `p`-layer.  Likewise `< x^m >` is dense in `< x >` for the
finite-quotient topology of any group in which `x` is conjugate to `x^m`,
so the machine edges are not closed in the enlarged base; the engine's
regular realization is necessarily abstract on `K`.

*Automorphism bookkeeping.*  On the free-product base `F = T_cal * F(b,d)`
(`T_cal` the central-HNN engine over `E`) both twists are restrictions of
automorphisms: `psi_i' = (Ad(x^-i mu) * delta_i)|`, `delta_i : d -> b_i d`,
and `t -> t d` extends to an automorphism `theta_p` of `F`.  But `theta_p`
and the `Xi_i = Ad(x^-i mu) * delta_i` do not commute, and on a direct-product
base `T_cal x F(b,d)` the map `t -> t d` is not an automorphism (it would
need `d` central).  So the two layers admit no common semidirect envelope
with a free action fixing the images of the `a_i`, and the residual
question is the corona conjugacy of the two `(2n+1)`-tuples
`(Phi(t), Phi(a_i))` and `(Phi(t)Phi(d), Phi(a_i))` in some regular
realization `Phi` of `Gamma_a'`.  This is the single analytic statement on
which both compiler routes now rest.

*Correction.*  `t -> t d` is an automorphism of `K * F(b,d)` and of `Lambda`,
but not of `T_cal * F(b,d)` or `K_M * F(b,d)`: the instruction relations
`r_i^-1 t(a,b) r_i = t(c,0)` would force `r_i^-1 d^((a,b)) r_i = d^((c,0))`,
false for a free letter `d`.  So the `p`-twist is an automorphism only of
the machine-free part; on the machine part it is entangled with every
instruction letter.

*Machine-free model.*  Eliminating `d = t^-1 p t p^-1` and `b_j = t_j^-1 p
t_j t^-1 p^-1 t` gives

```text
Gamma_a = < K_M * <p>, a_1..a_(2n) | [a_i,p] = 1, a_i t a_i^-1 = x^-i t x^i,
                                   a_i x a_i^-1 = x^m, [a_i, b_j] = 1 >,
```

and dropping the machine (`K_M -> < x, t >`) leaves the finitely presented
group `Gamma^K = < x, t, p, a_i | same >`, which already contains the
digit-reading edge and is not residually finite.  Whether `Gamma^K` is MF
is the smallest instance of the analytic question; a proof for it should
generalize, since the machine enters only through central HNN letters over
subgroups of `K`.

*Double machine.*  If the word component is a second machine letter `t'`
subject to the same instruction relations (`r_i^-1 t'(a,b) r_i = t'(c,0)`),
then `t -> t t'` is an automorphism of the double machine group and the
`p`-layer becomes a mapping torus, MF-safe by
[[crossed-product-by-corona-inner-automorphism-is-mf]] once the automorphism
is corona-inner.  The price is that appending a letter is now conjugation
by `x^-i mu` on both copies, so the evaluation map `t'(alpha,0) ->
w_alpha(c)` is no longer the restriction of an automorphism; the free
letters `b`, `d` are what make evaluation an automorphism (`b_j -> b_j c_j`),
and the `p`-edge is what makes them read digits.  The two requirements pull
in opposite directions, and no single envelope satisfies both.

*Consequence for the insertion edge.*  Since every finite quotient of
`Gamma_a` identifies `w_alpha(b)` with `w_(alpha+N)(b)`, condition `(c)` of
`(CF1)` fails for every nontrivial `C`: the finite quotients of the compiler
output kill `C` entirely, even when `C` is residually finite.  So the
insertion edge, too, must be handled by an abstract corona argument; the
graph shape from [[product-commuting-aanderaa-cohen-compiler]] remains the
right one for Shulman's Theorem 20, with the two embeddings of `A_+` given
by `(a,1)` and `(a, tau(a))` in `Gamma_a *_(A_+) (A_+ x C)`.

