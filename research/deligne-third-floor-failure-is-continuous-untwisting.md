---
rg: 2
id: deligne-third-floor-failure-is-continuous-untwisting
kind: claim
title: The third cellular floor fails exactly when a finitely approximable compact free Sp_4(Z)-space carries a continuous circle untwisting of the Deligne class, and every such space is non-profinite, non-Bernoulli and not untwistable with discrete phases
distinct_from:
  deligne-schreier-complexes-have-a-uniform-third-cellular-floor: that is the floor itself; this rewrites its failure as one dynamical object and derives constraints on every counterexample, without deciding the floor.
  deligne-multiplier-survives-on-bernoulli-times-profinite-actions: that excludes measurable untwisting on profinite and Bernoulli-times-profinite actions and lists incoherent finite-level voltage towers as a survivor; this shows that sup-norm towers are never incoherent, since they always cohere on a compact ultralimit system, and then feeds that system into (DM1).
  deligne-third-floor-holds-above-every-fixed-level: that bounds classes pulled back from a fixed level; this is about the limit system of an arbitrary counterexample sequence and uses no cohomology of finite-index subgroups beyond (L3).
  deligne-third-floor-has-no-polynomial-certificate: that kills algebraic certificates for proving the floor; this kills isotropy, discrete-phase, local-rule and Bernoulli-profinite constructions on the refutation side and isotropy arguments on the proof side.
  deligne-class-finite-action-norms-vanish: that is the Hamming problem for Z/3 torsor cochains; this is the sup-norm circle problem, and only a remark here transfers the method.
---

**ESTABLISHED** (`deligne-third-floor-failure-is-continuous-untwisting-proof`). Unreviewed.

## Setting

Notation of `deligne-opnorm-monomial-models-are-almost-flat-circle-bundles`: `Gamma = Sp_4(Z) = <S | R>`,
`Gamma~ = <S, z | [z,s], r z^(-k_r)>`, `E_3 = Gamma~ / <z^3>`, `T = R/Z`, and `mu_(1/3)(X)` for a finite `Gamma`-set `X`.
A monomial model is written `rho(s) e_x = e(a(x,s)) e_(s x)`.

- A **continuous untwisting** on a compact metrizable `Gamma`-space `K` is a continuous map `c : E_3 x K -> T` with
  `c(gh, y) = c(g, h y) + c(h, y)` (with `E_3` acting through `Gamma`) and `c(z, y) = 1/3` for all `y`. Equivalently,
  `E_3` acts continuously on `K x T` by `g(y, t) = (g y, t + c(g, y))` over the `Gamma`-action on `K`, with `z`
  acting as rotation by `1/3`.
- `K` is **finitely approximable** if there are finite `Gamma`-sets `X_n` and maps `pi_n : X_n -> K` with
  `max_(x, s in S) d(pi_n(s x), s pi_n(x)) -> 0`.
- `Gamma^bar = lim Gamma / Gamma(M)` is the congruence completion, on which `Gamma` acts freely.

## Statement

**(U) Reformulation.** `inf_X mu_(1/3)(X) = 0` (the floor fails) iff some finitely approximable compact metrizable
`Gamma`-space carries a continuous untwisting. When it fails, `K` can moreover be chosen with:
- the `Gamma`-action free at every point, with a `Gamma`-map `K -> Gamma^bar`;
- the maps `pi_n` exactly equivariant into a larger compact space, at uniform distance `-> 0` from `K`;
- a `Gamma`-invariant Borel probability measure (a weak* limit of the uniform measures on `X_n`).

**(C1) No finite orbits and vacuous isotropy.** No `K` as in (U) has a finite orbit. On the free `K` of (U) every
stabilizer is trivial, and its preimage `<z>` in `E_3` carries the character `z -> e(1/3)`. So restricting to a
stabilizer, or evaluating at a point of an ultralimit, never obstructs a counterexample.

**(C2) Discrete phases die.** Suppose `c` is continuously cohomologous on `K` to an untwisting whose values on
`S x K` are locally constant, for example one with values in a finite subgroup of `T`. Then `K` is not finitely
approximable. In particular, the Cantor system `K_3 = K_3''/<z>` is not finitely approximable.
- `K_3''` is the set of `omega in (Z/3)^(E_3)` with `omega(hz) = omega(h) + 1`, acted on by left translation.
- `K_3` carries the `mu_3`-valued untwisting `([omega], g) -> (omega(e) - omega(g^(-1)))/3`.
- `K_3` is a Cantor analogue of survivor 1 of `deligne-multiplier-survives-on-bernoulli-times-profinite-actions`
  (the `mu_3`-quotient of the Bernoulli shift of `E_3`); no isomorphism between them is claimed. The free space
  `K_3 x Gamma^bar` is not finitely approximable either.

**(C3) Every invariant measure is exotic.** For every `Gamma`-invariant probability `nu` on a `K` as in (U),
`(K, nu)` is not a measurable factor of any ergodic profinite action, any Bernoulli shift, or any Bernoulli times
ergodic profinite action.

**(C4) Fixed-radius local rules die.** Take a compact label space `A`, a radius `R`, a level `M` and a continuous rule
`F : A^(B_R) x Gamma/Gamma(M) -> T^S`, where `B_R` is the radius-`R` ball of `Gamma` in the word metric. Take finite
`Gamma`-sets `X_n` with labels `xi_n : X_n -> A` and `Gamma`-maps `q_n : X_n -> Gamma/Gamma(M)`. Set
`a_n(x, s) = F_s((xi_n(g x))_(g in B_R), q_n(x))`. Let `L` be the maximal relator length, and call
`p_n(x) = (xi_n(k x))_(k in B_(R+L))` the pattern at `x`. Suppose the realized pairs `(p_n(x), q_n(x))` become
Hausdorff-dense in `A^(B_(R+L)) x Gamma/Gamma(M)` as `n -> infinity`. Then `liminf eps(rho_n) > 0`. No injectivity is
assumed.
- Random i.i.d. labels of full support satisfy the density hypothesis with probability tending to 1. This needs,
  for each class `q`, a number of pairwise disjoint injective `(R+L)`-balls centred at points of class `q` that tends
  to infinity.
- So random local constructions of fixed radius with fixed congruence data cannot refute the floor, however the
  `X_n` are chosen.

## What this kills

**Named invariant.** The continuous untwisting `c` on the ultralimit system `K`, a compact free `Gamma`-space
with a circle bundle `K x T` on which `E_3` acts and `z` rotates by `1/3`.

**On the proof side: isotropy and point-evaluation arguments.** Such an argument takes a counterexample sequence,
evaluates the limiting phase field at one point of the limit (or restricts it to one stabilizer `Lambda_x`), and
contradicts (L3) there.
- **Where it dies.** It dies at the restriction to `Lambda_x`, because (L3) needs `Lambda_x` of finite index.
- A finite-index stabilizer occurs only when `|X_n|` stays bounded along the ultrafilter.
- After the product with `Gamma / Gamma(n!)` (step 3 of the proof), every stabilizer is trivial, and the character
  `z -> e(1/3)` of `<z>` exists.

**On the refutation side.** Every counterexample is a finitely approximable `K`. The following constructions die:
1. phase fields cohomologous to discrete ones (C2);
2. phase fields whose limit law is a factor of Bernoulli times profinite (C3);
3. fixed-radius random local rules over any `X_n` (C4).

**Coherence is automatic.** The (DM1) node lists "incoherent finite-level voltage towers" as a survivor, since they do
not come from one field on the profinite limit. In sup norm this distinction is empty: every tower with sup
frustration tending to 0 coheres to one continuous field on its own ultralimit system `K`. That system is not the
profinite limit, but by (C3) none of its invariant measures is Bernoulli times profinite. So the sup-norm form of
survivor 2 reduces to objects of survivor-1 type: free untwisted systems that are not Bernoulli times profinite. In
addition they must be finitely approximable and must have phases that are not cohomologous to discrete ones (C2).

## What is left

By (U), the floor is equivalent to the following statement.
- **(NFA) No finite approximation.** No finitely approximable compact metrizable `Gamma`-space carries a continuous
  untwisting of the Deligne class.

Compact free untwisted spaces do exist; `K_3 x Gamma^bar` from (C2) is one. By (C2) that one is not approximable. So (NFA) is about finite approximability, not about existence. It is a
sup-norm, circle-valued analogue of "sofic approximations cannot see the extension".

**(C2) alone cannot prove the floor (proved in step 6).** Two compact spaces carry a continuous untwisting none of
whose untwistings is continuously cohomologous to a locally constant one: a connected compact `Gamma`-space `K`, and
the free space `K x Gamma^bar`.
- Let `K''` be the set of `omega in T^(E_3)` with `omega(h z) = omega(h) + 1/3`, with `E_3` acting by left
  translation, and let `K = K''/<z>`.
- Put `c(g, [omega]) = omega(e) - omega(g^(-1))`.

The remaining content of (NFA) is whether spaces of this connected, non-discrete kind can be finitely
approximable.

**Remark (not part of the statement): the Hamming problem.** The same ultralimit construction runs with Loeb
measure in place of the sup norm, for Hamming-small `Z/3` torsor cochains
(`deligne-class-finite-action-norms-vanish`). It gives a measurable `mu_3`-valued untwisting on a pmp factor of a
Loeb limit of finite `Gamma`-sets. By (DM1) that factor is also not Bernoulli times profinite. So the sofic route
needs finitely approximable non-Bernoulli untwisted systems too. Loeb-measurability details were not written out.
