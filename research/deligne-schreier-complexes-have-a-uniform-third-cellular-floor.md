---
rg: 2
id: deligne-schreier-complexes-have-a-uniform-third-cellular-floor
kind: claim
title: Integral classes congruent to the Deligne class mod three have cellular norm bounded below uniformly over all Schreier complexes of Sp_4(Z)
distinct_from:
  deligne-opnorm-monomial-models-are-almost-flat-circle-bundles: that proves the duality and the floors for spherical and Kahler-proportional classes; this asks for the floor for all classes, the only open case being non-Kahler group classes of finite-index subgroups.
  deligne-finite-parameter-group-has-period-prime-to-three: that is about general operator-norm models on the finite branch; this is a necessary condition for the flagship, restricted to monomial models, and is independent of the branch.
  deligne-monomial-cover-models-have-a-detecting-cycle-floor: that floor tends to 0 along towers; this asks for a floor that does not.
---

**OPEN.** Notation of `deligne-opnorm-monomial-models-are-almost-flat-circle-bundles`. The claim is that some
`c > 0` works for every finite-index `Lambda <= Sp_4(Z)`, with `X = Gamma / Lambda`:

```text
||f_R||_cell >= c        for every f in kappa + 3 H^2(Y_X; Z).
```

By (L1) of that node, this is equivalent to `inf_X mu_(1/3)(X) > 0`. In words: no sequence of monomial
operator-norm `1/3`-models over exact `Gamma`-sets has defect tending to 0.

**Why it matters: it is necessary for the flagship.** Suppose the floor fails. (L1) gives monomial models `rho_n`
with `eps_n -> 0`. Put `U_n(g) = rho_n(w_g)` for fixed words `w_g`, with `w_e` empty.
- In `Gamma~`, `w_g w_h w_(gh)^(-1) = z^(b'(g,h))`, and the cocycle `b'` differs from the covering cocycle `b` of
  `deligne-sep7-norm-parameter-closed-subgroup` by an integral `delta lambda` with `lambda(e) = 0`.
- Rescale by `e(-lambda(g)/3)`. For a fixed pair `(g, h)`, the word `w_g w_h w_(gh)^(-1) z^(-b'(g,h))` is a product
  of `L(g, h)` conjugates of the relators `r z^(-k_r)` and `[z, s]`.
- So the pair defect is at most `L(g, h) eps_n -> 0`, and `1/3 in P_op`.

That refutes `deligne-triple-cover-exact-mf-radical`. So the flagship implies this claim, and a counterexample
here would be a counterexample to the flagship made of permutation-with-phase matrices.

**What remains after the established node.** By (K1) and (K2), only classes `f` of the following kind can violate
the floor:
- `f` is zero on `S_X`, so it is a class in `Hom(H_2(Lambda; Z), Z)`, congruent to `kappa` mod 3;
- `f_R` is not a real multiple of `kappa_R`.

Assume `pi_2` has finite `Z Gamma`-generation mass, which holds under type `F_3`. Then the claim is equivalent to:

```text
inf over Lambda and such non-Kahler integral group classes u of ||u_R||_cell > 0.
```

**How it can fail.** Congruence subgroups `Lambda_N` with integral classes `u_N = kappa + 3 g_N` such that:
- `(u_N)_R` is not proportional to `kappa_R`;
- `u_N` is small on every integral 2-cycle of bounded mass-to-value ratio;
- the size of `u_N` is carried by boundary (Eisenstein) or non-Kahler interior classes.

The torus model `T^2` with its `N x N` covers shows the mechanism is not vacuous for general complexes: there
the new classes of norm `1/N^2` are the whole story.

**A sufficient condition that can fail on its own.** A uniform circle cosystole: for all `X` and all integral
classes `u` of `Y_X` that vanish on `S_X` and are nonzero mod 3, `||u_R||_cell >= c`. This is `l^inf`-stability of
`Gamma` in the wreath products `T wr Sym(X)` with exact base.

It implies the claim together with (K1). A residual `f` vanishes on `S_X`, and it is nonzero mod 3 because
`f(Sigma) ≡ D` mod 3 with `3 not | D`, for the cycle `Sigma` of (L3). The condition forgets the congruence to
`kappa`, so it can fail while the claim holds. It has not been tested.

## Attempts
- **2026-09-18, swarm-0917-w13-w13-deligne-last1: posed.** It was split off from the period hole's monomial
  survivor after (K1), (K2) and (K3) of `deligne-opnorm-monomial-models-are-almost-flat-circle-bundles`. The
  natural next test is computational: an LP for `mu_(1/3)(Gamma / Lambda_N)` on the principal congruence quotients
  `Sp_4(Z/N)`, for small `N` prime to 3, from a certified finite presentation.
- **2026-09-19, swarm-0917-w14-w14-deligne-break: level-2 census and a character obstruction**
  (`deligne-third-floor-has-no-character-certificate`).
  - *Census (numerical MILP).* On the six solved `Sp_4(F_2)`-sets, `mu = 1/(291 D)`, the Kahler-proportional
    value. On the Weierstrass points and the 3+3 partitions (`D = 2`) this is exactly the (K2) floor `c_K = 1/582`.
    No non-Kahler class lowers it.
  - *Obstruction (proved).* `floor = dist(kappa/3, cl L)` in `C^2(Y; C(Sp_4(Z)^, R))`, and every continuous
    character trivial on `L` is trivial at `kappa/3`. So this claim is equivalent to non-dual-closedness of `cl L`
    at `kappa/3`, and no linear or detecting-cycle certificate, finite or profinite, can prove it. Already at
    level 2, `A_0 = 98 > 97` and `196 > 194`: the exact value beats every single-cycle bound.
  - Levels `N >= 3` were not solved exactly.
- **2026-09-19, swarm-0917-w14-w14-deligne-follow: fixed-level floor proved, sufficient condition corrected**
  (`deligne-third-floor-holds-above-every-fixed-level`, cohomology-index).
  - *Proved.* Fix any finite-index `Lambda_0`. Every class `f in kappa + 3 H^2` on any Schreier complex above
    `Gamma / Lambda_0` whose real part is pulled back from `Lambda_0` has `||f_R|| >= nu(Lambda_0) > 0`. This extends
    (K2) from level one to every level.
  - *Why.* Virtual divisibility of a fixed class is bounded by the finite profinite multiplier
    `H^2_cts(Lambda_0^, Q/Z)` of `sp4-finite-index-fd-projective-multiplier-is-finite`. Dividing pullbacks up a tower
    (the `T^2` mechanism above) is therefore dead.
  - *Refuted.* The sufficient condition above is false as written. At `Gamma(3)` a torsion class, not divisible by
    3, has `u_R = 0`. The repaired condition asks for `u(Z_2)` not contained in `3Z`, and it stays open.
  - *Left.* A counterexample must use classes new at each level. The open part is a bound on `nu` uniform in the
    level.
- **2026-09-19, swarm-0917-w15-w15-deligne-follow: every polynomial certificate dies**
  (`deligne-third-floor-has-no-polynomial-certificate`, linear-characteristic).
  - *Proved.* The w14 character kill extends to all degrees. Every continuous polynomial `P` on
    `E = C^2(Y; C(Sp_4(Z)^, R))` with `P(L) subset Z`, and every continuous polynomial phase trivial on `L`, is
    integral at `kappa/3`.
  - *Why.* A new finite-support lemma says an integer-valued bounded multilinear form on `C(Omega)` depends on
    finitely many points. The proof uses Bonami's inequality on the Rademacher chaos of the integer array, then a
    Hausdorff limit. Leafwise exactness on the finitely many leaves that meet the support then finishes.
  - *Finite levels.* Certificates of degree `<= k` and norm `<= b` depend on at most `R(k, b)` cells, so they
    collapse to detecting cycles on `R(k, b)` cells. These do not exist on `Gamma / Gamma(N)` once `N` is large. So
    no bounded family of algebraic certificates proves this claim.
  - *Also.* On any countable union of leaves, `kappa/3 + L` meets every neighbourhood of `0` for bounded pointwise
    convergence.
  - *Left.* A proof must be non-polynomial and non-local: min-max or rigidity over uncountably many leaves. The
    refutation side is unchanged.
