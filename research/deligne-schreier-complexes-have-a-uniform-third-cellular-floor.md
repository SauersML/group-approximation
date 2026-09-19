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
- **2026-09-19, swarm-0917-w15-w15-deligne-break (census-computation): the test was run. No counterexample was
  found, and it cannot certify lower bounds as posed.** Code and table are in
  `experiments/deligne-third-floor-level-census-2026-09-17/`.
  - *Presentation.* Birman-Hilden `Sp_4(Z) = Mod(S_2)/<<(t1 t2)^6>>` has 14 relators, each checked to be exact in
    `Sp_4(Z)`. The lift exponents from the `det u` winding are: chain6 `-3`, iota2 `-2`, sep `-1`, and 0 for the rest.
  - *Values.* `mu_(1/3)(pt) = 1/291` exactly (MILP closed). On `P^3(F_2)`, `Lag(F_2)` and `P^3(F_3)` the best
    certified upper bound is 1/291, which is the pulled-back point model.
    - That model is a fixed point of LP polishing.
    - Random starts end at 0.08-0.16.
    - No non-Kahler model beats the Kahler value on any set tried. This is weak evidence for the claim.
  - *Where the posed test dies.* An LP gives only upper bounds. The relaxation with real `n` is identically 0
    (`a = 0`, `n_c = -theta k_r`). By (L1), any lower bound is an `l^inf`-type closest-vector problem for the coset
    `kappa + 3 H^2(Y_X; Z)`, in a lattice of rank `10|X| - 1 + b_1(Y_X)`, which is at least 149 already at `|X| = 15`.
    HiGHS leaves the dual bound at 0 after 120 s at `|X| = 15`. Lower bounds need structure, such as the transfer
    relations of `mod-s2-induced-torelli-characters-have-positive-relation-floors`, not a larger computation.
