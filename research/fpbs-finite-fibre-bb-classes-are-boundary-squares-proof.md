---
rg: 2
id: fpbs-finite-fibre-bb-classes-are-boundary-squares-proof
kind: route
title: Fibre masses transform by the Radon--Nikodym cocycle, so finite fibres turn the boundary class into an invariant measure; minimality makes it infinite on open sets, a fibre-mass Halmos count transfers conservativity both ways, and the boundary action itself then satisfies the Bevilacqua--Bowen hypotheses
target: fpbs-finite-fibre-bb-classes-are-boundary-squares
requires:
  - fpbs-hyperbolic-bb-criterion-obstruction
  - fpbs-dini-boundary-class-diagonal-dissipative
  - fpbs-finite-measure-ray-codes-die-on-rank-one-lattices
---

Full written proof. All sets and maps are Borel, and statements hold up to null sets. Notation is as in the target
claim. `Gamma` is countable, so all unions over `Gamma` are countable.

## Standard facts used

- **(F1) Uniqueness of disintegration.** If `mu = ∫ mu_x d lambda_0 = ∫ mu'_x d lambda_0` with `mu_x`, `mu'_x`
  sigma-finite measures carried by `xi^{-1}(x)`, then `mu_x = mu'_x` for a.e. `x`. (Reduce to a finite measure
  `f mu` with `f > 0` integrable, where it is the usual uniqueness of conditional measures.)
- **(F2) Recurrence.** A measure-preserving action of a countable group on a sigma-finite space is conservative
  (no wandering set of positive measure) iff for every `E` of positive measure, a.e. `p` in `E` has `g p` in `E` for
  infinitely many `g`. For a nonnegative `f` this gives: if the action is conservative, then
  `sum_g f(g p) = infinity` for a.e. `p` in `{f > 0}`. (Apply the recurrence to `E = {f > epsilon}` for each
  rational `epsilon`.) For the Hopf decomposition `Con`, `Dis` see `fpbs-hyperbolic-bb-criterion-obstruction`,
  (H4).
- **(F3) Boundary dynamics.** For nonelementary hyperbolic `Gamma`, the action on `dGamma` is minimal, and there is
  no `Gamma`-invariant Borel probability measure on `dGamma`. (If `nu` were invariant, then for a loxodromic `g` with
  fixed points `g^±` north--south dynamics gives `g^n_* nu -> nu({g^-}) delta_{g^-} + (1 - nu({g^-})) delta_{g^+}`,
  so `nu` is carried by `{g^+, g^-}`. Two loxodromics with disjoint fixed-point pairs exist, a contradiction.)
- **(F4) Adams.** The action of a hyperbolic group on `dGamma` is amenable for every quasi-invariant measure class
  (S. Adams, Topology 33 (1994)). Amenability depends only on the measure class.
- **(F5) Glimm--Effros, Harrington--Kechris--Louveau.** If `E` is a non-smooth countable Borel equivalence relation on
  a Polish space, there is a continuous injection `f : 2^N -> X` with `a E_0 b` iff `f(a) E f(b)`.
- **(F6) Extension from a complete section.** Let `E` be a countable Borel equivalence relation on `X`, `Y ⊂ X`
  Borel, and `nu` an `E|_Y`-invariant sigma-finite measure on `Y`. Then there is a unique `E`-invariant measure
  `lambda` on the saturation `[Y]_E` with `lambda|_Y = nu`. It is sigma-finite, and it is ergodic when `nu` is
  (Kechris--Miller, *Topics in Orbit Equivalence*, Section 2: write `[Y]_E` as a countable union of images of partial
  Borel injections with graph in `E` and domain in `Y`, by Lusin--Novikov, and transport `nu`).
- **(BB) Bevilacqua--Bowen** (arXiv:2510.05459, Theorem 8.1 with Theorem `T:exact`), as recorded in
  `fpbs-hyperbolic-bb-criterion-obstruction`: a hyperbolic (hence exact) group with an amenable, ergodic, PDR imp
  action with infinite non-atomic ergodic components has max-cost at most one, hence fixed price one. A doubly
  recurrent action, that is one whose diagonal action on `Z x Z` is conservative, is PDR, since `Con(Z x Z)` is then
  conull and so is the relation it generates.

## Step 1: fibre masses transform by the cocycle

Let `r_g = d(g_* lambda_0) / d lambda_0`. Since `mu` is invariant,
`mu = g_* mu = ∫ g_* mu_x d lambda_0(x) = ∫ g_* mu_{g^{-1} y} r_g(y) d lambda_0(y)`.
The measure `g_* mu_{g^{-1} y}` is carried by `g xi^{-1}(g^{-1} y) = xi^{-1}(y)`, by equivariance of `xi`. By (F1),

  (1.1)  `g_* mu_{g^{-1} y} = r_g(y)^{-1} mu_y`  for a.e. `y`, for each `g`.

**Proof of Theorem 1.** Let `I = {x : mu_x(Z) < infinity}`. By (1.1), `x ∈ I` iff `g x ∈ I` for a.e. `x`, since
`r_g` is finite and positive a.e. So `I` is `Gamma`-invariant mod null sets. Since `Z` is ergodic, so is `C` (the
preimage of an invariant set is invariant). Hence `I` is null or conull. ∎

## Step 2: the invariant measure (Theorem 2, first part)

Assume the fibres are finite and put `h(x) = mu_x(Z)`, finite and positive a.e. Taking total masses in (1.1),
`h(g^{-1} y) = r_g(y)^{-1} h(y)`. So, for Borel `A`,

  `g_*(h lambda_0)(A) = ∫_{g^{-1}A} h d lambda_0 = ∫_A h(g^{-1} y) r_g(y) d lambda_0(y) = ∫_A h d lambda_0.`

Thus `lambda = h lambda_0` is invariant. It is sigma-finite (`h` is finite a.e.), equivalent to `lambda_0` (`h > 0`),
ergodic (its class is `C`), and nonatomic whenever `C` is. (If `C` had an atom, ergodicity would put it on one
orbit; the claim assumes nonatomic, as do all BB certificates, `fpbs-hyperbolic-bb-criterion-obstruction`
Step 7.) By (F3), `lambda` is infinite.

**Infinite on every open set.** The support of `lambda` is closed and invariant, hence equal to `dGamma` by
minimality. Suppose `lambda(U) < infinity` for some nonempty open `U`. By minimality `dGamma = ∪_g g U`, and by
compactness `dGamma = g_1 U ∪ ... ∪ g_k U`. Invariance gives `lambda(dGamma) <= k lambda(U) < infinity`, and
`lambda / lambda(dGamma)` is an invariant probability, contradicting (F3). So `lambda(U) = infinity`.

Consequently `lambda x lambda (U x V) = infinity` for all nonempty open `U`, `V`. Every point of `d^2 Gamma` has a
neighbourhood basis of such products, so `lambda x lambda` is Radon at no point. On the flow space
`d^2 Gamma x R` (any proper cocompact model; for a lattice in a rank-one Lie group, `T^1 X`), the flow measure
`lambda x lambda x dt` gives infinite mass to every open set, and so does its image on the compact quotient. So
`lambda x lambda` is a sigma-finite invariant measure in the class of `C x C` that is not a current in the Radon sense
of `fpbs-finite-measure-ray-codes-die-on-rank-one-lattices`.

## Step 3: conservativity transfers both ways (Theorem 2.2)

Let `D = d^2 Gamma = dGamma^2 \ Delta` with `m = lambda x lambda`, and `pi = xi x xi : W -> D`. For `p = (x,y)` put
`M_p = h(x)^{-1} h(y)^{-1} (mu_x x mu_y)`, a probability measure on `pi^{-1}(p)`. Then

  `mu x mu |_W = ∫_D H(p) M_p d lambda_0^2(p) = ∫_D M_p dm(p)`, where `H(x,y) = h(x) h(y)`,

so `pi` is measure preserving onto `(D, m)` with probability fibres. By (1.1) and Step 2,
`g_* M_p = M_{g p}` for a.e. `p`, for each `g` (the factors `r_g^{-1}` cancel against the change in `h`).

*Downward.* If `A ⊂ D` is wandering for `m`, then `pi^{-1}(A)` is wandering in `W`, with the same positivity. So
`Con(W) ⊂ pi^{-1}(Con(D, m))`.

*Upward.* Suppose `Gamma` is conservative on a Borel invariant set `D_1 ⊂ D`, and let `A ⊂ pi^{-1}(D_1)` be
wandering in `W`. Put `f(p) = M_p(A)`. For a.e. `p`,

  `sum_g f(g^{-1} p) = sum_g M_{g^{-1} p}(A) = sum_g M_p(g A) <= M_p(W) = 1,`

because the sets `gA` are disjoint. By (F2) applied to the conservative action on `D_1` and the function `f`, the sum
is infinite a.e. on `{f > 0}`. So `f = 0` a.e., and `mu x mu (A) = ∫ f dm = 0`. Hence `pi^{-1}(D_1) ⊂ Con(W)`.

Taking `D_1 = Con(D, m)` gives `Con(W) = pi^{-1}(Con(D, m))`. In particular `W` is conservative iff `(D, m)` is. ∎

## Step 4: a conservative square is a certificate (Theorem 3)

Let `lambda` be ergodic, nonatomic, sigma-finite and invariant, with conservative square. Put `Z = (dGamma, lambda)`.
- It is imp: `lambda` is invariant and, by (F3), infinite.
- It is ergodic, with one infinite non-atomic ergodic component.
- It is amenable by (F4), applied to a probability measure equivalent to `lambda`.
- The diagonal `lambda x lambda (Delta) = 0`, since `lambda` is nonatomic (Fubini). So the diagonal action on
  `Z x Z` coincides mod null sets with the action on `(D, m)`, which is conservative. So `Z` is doubly recurrent,
  hence PDR.
By (BB), `Gamma` has fixed price one. ∎

## Step 5: equivalence (Corollary 4)

(1 => 2): by Steps 2 and 3, the measure `lambda = h lambda_0` has conservative square on `D`, and `Delta` is null.
(2 => 1): take `Z = (dGamma, lambda)` and `xi = id`. The disintegration of `lambda` over a probability `lambda_0`
in its class is `mu_x = (d lambda / d lambda_0)(x) delta_x`, which is finite, and the crossing diagonal is `(D, m)`. ∎

## Step 6: the class is not empty (Proposition 5)

Let `E` be the orbit relation of `Gamma` on `dGamma`. A Patterson--Sullivan measure is ergodic, nonatomic and
quasi-invariant, so `E` is not smooth (a Borel transversal would meet a.e. orbit once, and an ergodic quasi-invariant
measure would then be carried by one orbit, hence atomic). By (F5) there is a continuous injection `f : 2^N -> dGamma`
with `a E_0 b` iff `f(a) E f(b)`. Let `Y = f(2^N)` and `nu = f_* beta`, where `beta` is the uniform Bernoulli measure,
which is `E_0`-invariant and ergodic. Then `nu` is `E|_Y`-invariant and ergodic, and by (F6) it extends to an
`E`-invariant sigma-finite ergodic measure `lambda` on `[Y]_E` (extended by zero). Each `g` in `Gamma` has graph in
`E`, so `E`-invariance gives `Gamma`-invariance. Every point of `[Y]_E` is the image of a point of `Y` under one of
countably many partial injections with graph in `E`, so an atom of `lambda` would give an atom of `nu`; hence `lambda`
is nonatomic. By (F3) it is infinite. ∎

## Step 7: filters and calibration (Corollary 6)

1. *Dini.* Apply Theorem C of `fpbs-dini-boundary-class-diagonal-dissipative` to the class of `lambda`. If it is
   absolutely continuous with respect to one finite Dini measure, then Theorem B applies to `Z = (dGamma, lambda)`
   with `xi = id`, and the crossing diagonal, which is `(D, m)` mod null sets, is totally dissipative. So a
   conservative square forces the second alternative: the class is singular to every Dini measure. By the last clause
   of Theorem C no finite restriction has positive lower local dimension on a positive set.
2. *Cost.* If `Gamma` has a free pmp action of cost `> 1`, it does not have fixed price one, so by Theorem 3 no
   such `lambda` has a conservative square. For `beta_1^(2)(Gamma) > 0` every free pmp action has cost
   `>= 1 + beta_1^(2) > 1` (Gaboriau). This covers `F_r` (`r >= 2`) and closed surface groups. It is consistent
   with the known values and removes no case that should survive.
3. *Radon.* Step 2 shows the invariant measure forced in `C x C` is nowhere Radon. The zero-entropy and
   positive-entropy arguments of `fpbs-finite-measure-ray-codes-die-on-rank-one-lattices` use a finite flow measure,
   and here the flow measure of every open set is infinite, so they do not apply.

## What the proof does not give

- It proves nothing about infinite fibres (Theorem 1, second case), for example Maharam extensions of type III
  classes, where `C x C` need not carry any sigma-finite invariant measure.
- It does not decide the square problem (II_inf-square). The only known obstruction is the shadow-product count of
  the Dini node, which uses the size of the class but not its invariance. The next test is whether invariance of
  `lambda` (every small shadow `O(g)` is the image of a large set of equal measure) forces the shadow-product sum of
  finite restrictions of `lambda` to converge.
