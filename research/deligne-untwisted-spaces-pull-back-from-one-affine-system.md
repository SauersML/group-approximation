---
rg: 2
id: deligne-untwisted-spaces-pull-back-from-one-affine-system
kind: claim
title: Every continuous circle untwisting of a class in H^2(Gamma;T) is pulled back from one explicit affine system on T^Gamma/T, so the third cellular floor is the statement that this single system has no approximate periodic points
distinct_from:
  deligne-third-floor-failure-is-continuous-untwisting: that rewrites floor failure as "some finitely approximable compact space carries a continuous untwisting", an existential over all compact Gamma-spaces; this removes that quantifier by exhibiting one universal space through which every untwisting factors, and adds the group structure of the finitely visible classes.
  central-extension-untwisting-over-boundaries: that is an obstruction to untwisting over boundary actions with the kernel acting freely; this is a universal-object statement for continuous untwistings over arbitrary compact spaces and says nothing about boundaries.
  deligne-monomial-parameter-group-is-governed-by-maslov-slope: that studies the closed subgroup of monomial Maslov parameters through the defect function; this gives the dynamical model of the same question at one parameter and the subgroup property for all of H^2(Gamma;T), with no slope or defect estimates.
---

**ESTABLISHED** (`deligne-untwisted-spaces-pull-back-from-one-affine-system-proof`). Unreviewed.

## Setting

`Gamma` is any countable group, `T = R/Z` written additively, and `beta : Gamma x Gamma -> T` is a normalized
2-cocycle: `beta(a,b) + beta(ab,c) = beta(a,bc) + beta(b,c)` and `beta(e,g) = beta(g,e) = 0`.

- A **continuous `beta`-untwisting** on a compact metrizable `Gamma`-space `K` is a continuous
  `c : Gamma x K -> T` with `c(gh, y) = c(g, h y) + c(h, y) + beta(g, h)`.
- **Finitely approximable** is as in `deligne-third-floor-failure-is-continuous-untwisting`: finite `Gamma`-sets
  `X_n` and maps `pi_n : X_n -> K` with `max_(x, s in S) d(pi_n(s x), s pi_n(x)) -> 0`. Equivalently, `K` has
  approximate periodic orbits of every precision.

**The affine system.** Let `U_beta = T^Gamma / T`, the product torus modulo constant functions, with

```text
(g . omega)(h) = omega(g^(-1) h) + beta(h^(-1), g)            (A)
c_U(g, [omega]) = omega(e) - omega(g^(-1)).                    (C)
```

`U_beta` is a compact abelian group, the Pontryagin dual of the augmentation ideal of `Z[Gamma]`. `Gamma` acts on
it by affine homeomorphisms whose linear part is the shift on `T^Gamma / T`. Under the connecting isomorphism
`H^1(Gamma; T^Gamma / T) = H^2(Gamma; T)`, the translation part corresponds to `[beta]`, up to the sign convention.

## Statement

1. **(Action and untwisting.)** (A) is a continuous action of `Gamma` on `U_beta` by affine homeomorphisms, and
   (C) is a continuous `beta`-untwisting on `U_beta`.
2. **(Universality.)** Let `c` be any continuous `beta`-untwisting on any compact metrizable `Gamma`-space `K`.
   Then `Phi_c(y) = [h -> -c(h^(-1), y)]` is a continuous `Gamma`-map `K -> U_beta` with `c = Phi_c^* c_U`.
3. **(Only the class matters.)** If `beta' = beta + delta lambda`, then untwistings of `beta` and `beta'` on the
   same `K` correspond through `c' = c - lambda`. So `U_beta` and `U_beta'` are finitely approximable together.
4. **(Group of finitely visible classes.)** The set
   `M(Gamma) = { theta in H^2(Gamma; T) : U_theta is finitely approximable }`
   is a subgroup. It equals the set of classes carrying a continuous untwisting on some finitely approximable
   compact space. It contains every class that vanishes on some finite-index subgroup.
5. **(The third floor, one explicit system.)** For `Gamma = Sp_4(Z)`, let `theta_D` be the image in `H^2(Gamma;T)`
   of the class of Deligne's triple cover `E_3` under `Z/3 -> T`, `1 -> 1/3`. Then
   `deligne-schreier-complexes-have-a-uniform-third-cellular-floor` is equivalent to `theta_D not in M(Gamma)`.
   In words: some `delta_0 > 0` satisfies `max_(x, s in S) d(pi(s x), s pi(x)) >= delta_0` for every finite
   `Gamma`-set `X` and every map `pi : X -> U_(theta_D)`. The floor says that the affine system has no approximate
   periodic points. Deligne's theorem says it has no exact ones.

## What this changes

- **The existential over spaces in (NFA) collapses.** (NFA) of `deligne-third-floor-failure-is-continuous-untwisting`
  quantifies over all compact `Gamma`-spaces. By item 2, finite approximability passes to continuous equivariant
  images. So (NFA) holds iff the one space `U_(theta_D)` is not finitely approximable. The connected space `K` and
  the Cantor space `K_3` of that node both map to `U_(theta_D)` by `Phi_c`.
- **Refutation side.** Building exotic compact spaces is never needed. A counterexample to the floor, and so to the
  flagship `deligne-triple-cover-exact-mf-radical`, is exactly a sequence of approximately equivariant maps from
  finite `Gamma`-sets into this one affine torus system.
- **Proof side.** It is enough to prove that one explicit affine algebraic action has no approximate periodic
  points. Its linear part, the shift on `T^Gamma / T`, has dense exact periodic points: for `f : Gamma/Lambda -> T`,
  the map `x -> [h -> f(h^(-1) x)]` is exactly equivariant. So the whole obstruction is carried by the translation
  class. Items 3-4 show it depends only on `theta_D` in the group `H^2(Gamma;T) / M(Gamma)`.
- **Calibration.** The metaplectic class `theta_M` (Maslov class over two) lies in `M(Gamma)`. By
  `deligne-covers-of-sp2g-z-have-finite-residual-2z` it vanishes on a finite-index subgroup, so it has exact
  finite orbits by item 4. Both systems have the same linear part. Any proof
  that `theta_D` is not in `M(Gamma)` must separate them through the translation class alone, which agrees with
  the w18 calibration of the period hole.

## What it does not do

It decides neither the floor nor the flagship. It is a reformulation with a universal object and a subgroup
structure. The open question is unchanged in difficulty: whether `U_(theta_D)` has approximate periodic orbits.
