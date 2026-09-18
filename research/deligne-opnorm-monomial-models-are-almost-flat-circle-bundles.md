---
rg: 2
id: deligne-opnorm-monomial-models-are-almost-flat-circle-bundles
kind: claim
title: Operator-norm monomial 1/3-models of a Deligne cover are almost-flat circle bundles on Schreier complexes, and spherical or Kahler-proportional Chern classes give defect floors uniform in the Gamma-set
distinct_from:
  deligne-monomial-cover-models-have-a-detecting-cycle-floor: that gives the HS floor 4 nu / A from one detecting cycle of mass A, a floor that tends to 0 along towers of covers; this is an exact l-infinity duality for the operator-norm defect and gives floors independent of the Gamma-set for two whole classes of Chern classes.
  deligne-congruence-monomial-models-need-growing-defect: that bounds HS defect below over normal congruence quotients at g >= 3; this is operator norm, any finite Gamma-set with any stabilizers, and genus two.
  deligne-parameter-group-is-a-virtual-invariant: that shows the virtual divisibility set of the Maslov class is {+-1,+-2} for general models; this proves the monomial analogue D(Lambda) in {1,2} for the cellular class on every Schreier complex and turns it into a uniform defect floor.
  deligne-finite-parameter-group-has-period-prime-to-three: that is the open period hole for general models; this settles part of its monomial survivor and isolates the rest.
---

**ESTABLISHED** (`deligne-opnorm-monomial-models-almost-flat-proof`). Unreviewed.

**Setting.** `Gamma = Sp_4(Z) = <S | R>` is a finite presentation. The universal-cover lattice is
`Gamma~ = <S, z | [z, s] (s in S), r z^(-k_r) (r in R)>`, with `z` of infinite order. Its quotients
`Gamma_n = Gamma~ / <z^n>` are the Deligne covers. Write `e(t) = exp(2 pi i t)`.

For a finite `Gamma`-set `X`, `Y_X` is the Schreier 2-complex:
- vertices `X`;
- an edge `(x, s)` from `x` to `s.x`;
- a 2-cell `(x, r)` along the loop reading `r` at `x`.

The following notation is used throughout.
- `k` is the integral 2-cochain `k(x, r) = k_r`. It is a cocycle, because `Y_X` has no 3-cells.
- `kappa = [k]` is its class in `H^2(Y_X; Z)`, and `kappa_R` is its image in `H^2(Y_X; R)`.
- `Y = Y_pt` is the presentation complex, and `p : Y~ -> Y_X` is the universal covering (the Cayley complex).
- `S_X = p_* Z_2(Y~; Z)` is the spherical part of `H_2(Y_X; Z) = Z_2(Y_X; Z)`.

For a real class `c`, the **cellular norm** is `||c||_cell = min { ||v||_inf : v a cocycle representing c }`.
It is a norm on `H^2(Y_X; R)`.

A **monomial `theta`-model over `X`** has:
- `rho(z) = e(theta) I` on `l^2(X)`;
- `rho(s) = D_s P_s`, where the permutations `P_s` realize the action on `X` *exactly*, and `D_s` is diagonal
  with entries `e(a(x, s))`.

Its operator-norm defect is `eps(rho) = max_r || rho(r) e(-theta k_r) - I ||_op`.
- A *block* model with block size `b` instead uses `P_s (x) I_b` and block-diagonal `D_s` with `U(b)`-blocks.
- Put `mu_theta(X) = inf_rho max_(x,r) dist((delta a)(x, r) - theta k_r, Z)`, the infimum over all monomial models.

**Theorem.** Let `X = Gamma / Lambda` be transitive. A disjoint union takes the maximum over its orbits.

**(L1) Exact duality.** Every monomial `theta`-model satisfies `4 mu_theta(X) <= eps(rho)`, and some model
attains `eps = |e(mu_theta(X)) - 1| <= 2 pi mu_theta(X)`. For `theta = 1/q`:

```text
mu_(1/q)(X) = (1/q) min { ||f_R||_cell : f in kappa + q H^2(Y_X; Z) },
||c||_cell  = max { c(Sigma) / |Sigma|_1 : 0 != Sigma in Z_2(Y_X; Z) }.
```

In words, monomial `1/q`-models of defect `eps` are the same as `(q eps / 4)`-flat `T`-connections on the
circle bundle over `Y_X` whose Chern class is `kappa` mod `q`.

**(L2) Pulled-back classes keep their norm.** If `pi : X' -> X` is a `Gamma`-map, then
`||pi^* c||_cell = ||c||_cell` for every `c` in `H^2(Y_X; R)`.

**(L3) The invariant `D`.** `kappa(Z_2(Y_X; Z)) = D(Lambda) Z`, where `D(Lambda)` is the order of `z` in
`H_1(Lambda~; Z)` and `Lambda~` is the preimage of `Lambda` in `Gamma~`. Moreover `D(Lambda)` lies in `{1, 2}`
for every finite-index `Lambda`. In particular `kappa_R != 0` on `Y`, and `c_K := ||kappa_R||_(cell, Y) / 6 > 0`
is a constant of the presentation.

**(K1) Spherical kill.** `kappa` vanishes on `S_X`. Suppose `pi_2(Y)` is generated as a `Z Gamma`-module by
2-spheres `sigma_1, ..., sigma_p` in `Y~` of cellular mass at most `M_0`. Then any `f in kappa + 3 H^2(Y_X; Z)`
with `f|S_X != 0` has `||f_R||_cell >= 3 / M_0`.

**(K2) Kahler-proportional kill.** Any `f in kappa + 3 H^2(Y_X; Z)` with `f_R in R kappa_R` has
`||f_R||_cell >= 3 c_K`.

**(K3) Block reduction.** A block `1/3`-model with block size `b`, `3 not | b`, has `eps >= 4 mu_(1/3)(X) / b`.

**Corollary (uniform floor away from the residual class).** Let `rho` be a monomial `1/3`-model over any finite
`Gamma`-set. Suppose no `f in kappa + 3 H^2(Y_X; Z)` with `||f_R||_cell <= 3 eps / 4` is both
- zero on `S_X`, and
- not proportional to `kappa_R` over `R`.

Then `eps >= 4 min(1 / M_0, c_K)`, with `1 / M_0 := 0` if no finite `M_0` exists. The same holds divided by `b`
for block models with `3 not | b`.

By Hopf's theorem `H_2(Y_X; Z) / S_X = H_2(Lambda; Z)`. So a class that survives is an integral class of
`Lambda` itself, congruent to `kappa` mod 3 and not a real multiple of the Kahler class. Examples are
Eisenstein and boundary classes, and non-Kahler interior `(1,1)`-classes of congruence subgroups.

**Remarks (not part of the established statement).**
- A finite `M_0` exists when `Gamma` has type `F_3`: then `pi_2` of a finite presentation complex is finitely
  generated over `Z Gamma`. Arithmetic groups are of type `F_infinity` (Borel-Serre). No verbatim node imports
  this yet.
- (K2) is uniform in `X`, including sequences whose stabilizers change with index going to infinity. That is
  exactly the survivor left by w8-last1 in the period hole.
- A parallel lane in the same wave (swarm-0917-w13-deligne-break, `mod-s2-induced-torelli-characters-have-positive-relation-floors`,
  not landed when this was written) proved the same duality for characters induced from `Lambda >= I`. Its floor
  comes from one positive relation, of mass about `5 [Sp_4 : Gamma']`, and dies when `3` divides the index. (K2)
  here is uniform in `X` whatever the index, but it covers only Kahler-proportional classes.
- The detecting-cycle floors of `deligne-monomial-cover-models-have-a-detecting-cycle-floor` tend to 0 along
  towers. (L1) and (L2) explain this: pulled-back classes keep their norm while detecting cycles get longer.
