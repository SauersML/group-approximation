---
rg: 2
id: fpbs-rank-one-lebesgue-boundary-diagonal-dissipative-proof
kind: route
title: Inducing to the ambient rank-one group makes the fibre measure scale under A, a scaling flow has a measurable height, and the mean height on each crossing line is an equivariant point of the symmetric space
target: fpbs-rank-one-lebesgue-boundary-diagonal-dissipative
requires:
  - fpbs-hyperbolic-bb-criterion-obstruction
---

Full written proof. All maps are Borel. "Conull" refers to the stated measure.

## Imported inputs

- **(R1) Rank-one structure.** `G = K A N` (Iwasawa), `P = M A N` is the stabilizer of the base point `e P` of
  `dX = G/P`. `M = Z_K(A)` is compact and fixes the base point `o = eK`. `N^-` is the opposite unipotent group, and
  `A = {a_s}` is one-dimensional. `MA = P ∩ P^-` is the stabilizer of the ordered pair `(eP, wP)`, where
  `w in N_K(A)` satisfies `w a_s w^{-1} = a_{-s}`. `w` normalizes `M`. The standard line `ell_0 = {a_s o}` joins
  `eP` to `wP`.
  - `G` acts transitively on ordered pairs of distinct points of `dX`, with stabilizer conjugate to `MA`.
  - `N` acts simply transitively on `dX \ {eP}`, by a diffeomorphism `n ↦ n wP`.
  - The big cell `Omega = N^- eP` is open and conull for `Leb`, and `N^- -> Omega` is a diffeomorphism.
  - Conjugation by `a_s` scales Haar measure of `N^-` by `delta(a_s) = e^{c s}` with `c = -(m_alpha + 2 m_{2alpha})`
    or its negative (the sign depends on convention). In any case `c != 0`, and `delta(m) = 1` for `m in M`.
- **(R2) Quasi-invariant classes on homogeneous spaces (Mackey).** The null ideal of a sigma-finite measure on `G/P`
  that is `G`-invariant as an ideal is the null ideal of `Leb`.
- **(R3) Invariant measures on a group factor.** A sigma-finite measure on `N^- x Y` invariant under left translation
  in the first factor equals `Haar(N^-) x nu` for a sigma-finite `nu` on `Y` (disintegrate over `Y`; an invariant
  sigma-finite measure on a Lie group is a multiple of Haar).
- **(R4) Lemma 0** of `fpbs-hyperbolic-bb-criterion-obstruction-proof`. Its proof uses only Halmos recurrence on
  `Con`, so it holds verbatim for any countable group. If `D` is an invariant set carrying a measurable equivariant map
  `M` to finite nonempty subsets of the group, then `D ∩ Con` is null.
- Fubini, and the correspondence between `G`-invariant Borel subsets of `G x_Gamma Z` and `Gamma`-invariant Borel
  subsets of `Z` (`S ↦ {z : [e,z] in S}`), which preserves nullity.

## Step 1: the induced space and its fibre

Let `Zhat = G x_Gamma Z` be the quotient of `G x Z` by `(g,z)γ = (gγ, γ^{-1}z)`, with `G` acting on the left. Since
`Gamma` is discrete, `Haar x mu` restricted to `F x Z` (a Borel fundamental domain `F`) defines a `G`-invariant
sigma-finite measure `muhat`. Define `pi([g,z]) = g xi(z)`. It is well defined and `G`-equivariant.

The null ideal `{E : muhat(pi^{-1}E) = 0}` is `G`-invariant, and it is the null ideal of `pi_* muhat'` for a finite
measure `muhat'` equivalent to `muhat`. By (R2) it is the `Leb` ideal. So `pi^{-1}(Omega)` is conull.

Let `Y = pi^{-1}(eP)`. `P` acts on `Y`. The map `Psi : N^- x Y -> pi^{-1}(Omega)`, `(n,y) ↦ n y`, is a Borel bijection.
Its inverse is `zhat ↦ (n(pi zhat), n(pi zhat)^{-1} zhat)`, where `n : Omega -> N^-` is the inverse of (R1). The
pullback `Psi^* muhat` is invariant under left translation of `N^-`. By (R3) it equals `Haar(N^-) x nu`.

**Lemma 1 (scaling).** `nu(a E) = delta(a)^{-1} nu(E)` for `a in A`, and `nu(mE) = nu(E)` for `m in M`.

*Proof.* `a Psi(n,y) = a n y = (a n a^{-1})(a y) = Psi(a n a^{-1}, a y)`. Invariance of `muhat` gives
`Haar(a S a^{-1}) nu(aE) = Haar(S) nu(E)` for `S` of finite positive Haar measure. Apply (R1). The same computation
works for `M`.

After replacing `s` by `-s` if needed, `nu(a_s E) = e^{-cs} nu(E)` with `c > 0`. In particular `nu` is
`MA`-quasi-invariant.

## Step 2: a measurable height on the fibre

**Lemma 2.** There is an `MA`-invariant conull Borel set `Y_0 ⊂ Y` and a Borel `h : Y_0 -> R` with
`h(a_s y) = h(y) + s` and `h(m y) = h(y)` for all `y in Y_0`, `s in R`, `m in M`.

*Proof.* Fix increasing Borel sets `B_k` of finite measure with union `Y`.
- **Finite backward occupation.** Put `phi_k(y) = ∫_0^∞ 1_{B_k}(a_{-s} y) ds`. For `B'` of finite measure,
  `∫_{B'} phi_k dnu = ∫_0^∞ nu(B' ∩ a_s B_k) ds <= ∫_0^∞ e^{-cs} nu(B_k) ds < ∞`. So `phi_k < ∞` `nu`-a.e.
- **Invariance of the good set.** `phi_k(a_t y) = ∫_{-∞}^t 1_{B_k}(a_u y) du`. This is nondecreasing and
  1-Lipschitz in `t`, tends to 0 as `t -> -∞`, and finiteness of `phi_k` is `A`-invariant.
- **Total occupation.** `T_k(y) = ∫_R 1_{B_k}(a_u y) du` is `A`-invariant and increases in `k`. By Fubini and
  quasi-invariance, for a.e. `y` we have `a_u y in ∪ B_k` for a.e. `u`, so `T_k(y) -> ∞`.
- **The height.** Let `Y_0'` be the `A`-invariant conull set where every `phi_k` is finite and `T_k -> ∞`. Put
  `k(y) = min{k : T_k(y) > 1}`, which is `A`-invariant, and
  `h_0(y) = -sup{t in Q : phi_{k(y)}(a_t y) <= 1}`.
  The set of such `t` is nonempty and bounded above, and the supremum over rationals equals the supremum over reals
  by continuity.
- **Equivariance.** `sup{t : phi(a_{t+r} y) <= 1} = sup{u : phi(a_u y) <= 1} - r`, so `h_0(a_r y) = h_0(y) + r`.
- **`M`-invariance.** `M` commutes with `A` and preserves `nu`. Let
  `Y_0 = {y in Y_0' : Haar_M{m : m y notin Y_0'} = 0}`. It is conull by Fubini, and `A`- and `M`-invariant. Set
  `h(y) = inf{v : Haar_M{m : h_0(m y) <= v} >= 1/2}`, the median. Translating `h_0` by `s` translates the median by
  `s`, and the right-invariance of Haar measure gives `h(m' y) = h(y)`. Borel measurability follows by Fubini.

## Step 3: the equivariant midpoint

Fix a Borel section `sigma` on ordered pairs of distinct boundary points, with `sigma(theta, theta')(eP, wP) =
(theta, theta')`. For `zhat, zhat'` in `Zhat` with `pi(zhat) != pi(zhat')`, put `g_0 = sigma(pi zhat, pi zhat')`,
`y_1 = g_0^{-1} zhat` and `y_2 = w^{-1} g_0^{-1} zhat'`. Both lie in `Y`. On the set `D_F` where both lie in `Y_0`,
define
`Fhat(zhat, zhat') = g_0 a_{mu} o`, where `mu = (h(y_1) - h(y_2))/2`.

**Lemma 3.** `D_F` and `Fhat` do not depend on the choice of `g_0` in its coset `g_0 MA`. Hence
`Fhat(g zhat, g zhat') = g Fhat(zhat, zhat')` for all `g in G`, and `D_F` is `G`-invariant.

*Proof.* Replace `g_0` by `g_0 m a_t`.
- Then `y_1` becomes `a_{-t} m^{-1} y_1`, so `h(y_1)` becomes `h(y_1) - t`.
- `y_2` becomes `(w^{-1} a_{-t} w)(w^{-1} m^{-1} w) y_2 = a_t m'' y_2` with `m'' in M`, so `h(y_2)` becomes
  `h(y_2) + t`.
- Membership in `Y_0` is unchanged, because `Y_0` is `MA`-invariant.
- `mu` becomes `mu - t`, and the point becomes `g_0 m a_t a_{mu - t} o = g_0 m a_mu o = g_0 a_mu m o = g_0 a_mu o`.

Equivariance follows, since `g sigma(theta, theta')` is a valid choice for the pair `(g theta, g theta')`.

## Step 4: descent to `Gamma` and the conullity check

For `z` in `Z` put `iota(z) = [e,z]`. Then `iota(γ z) = [γ, z] = γ iota(z)`. Let
`U = {(z,z') : xi(z) != xi(z')}`. Since `xi_* mu << Leb` and the diagonal of `dX x dX` is `Leb x Leb`-null, `U` is
conull for `mu x mu`. Set
`D' = {(z,z') in U : (iota z, iota z') in D_F}` and `f(z,z') = Fhat(iota z, iota z')`.

By Lemma 3, `D'` is `Gamma`-invariant and `f(γ z, γ z') = γ f(z,z')` exactly. It remains to prove that `D'` is
conull.

**Lemma 4.** Let `S_good` be the set of `zhat` such that, for Haar-a.e. `g in G` with `g zhat in pi^{-1}(Omega)`,
the `Y`-coordinate of `Psi^{-1}(g zhat)` lies in `Y_0`. Then:
1. `S_good` is `G`-invariant, Borel and conull.
2. If `y in Y ∩ S_good`, then `Haar_N{n : n y notin Y_0} = 0`.

*Proof.*
1. `G`-invariance comes from the invariance of Haar measure. The Borel property comes from Fubini. For conullity: for
   each fixed `g`, the set of `zhat` whose `g`-translate has bad coordinate is `g^{-1} Psi(N^- x (Y \ Y_0))`, which
   is null. Now apply Fubini on `G x Zhat`.
2. Almost every `g` lies in the big cell `N^- P`. If `g = n^- p`, then `g y = n^-(p y)` with `p y in Y`, so the
   coordinate is `p y`. Hence `Haar_P{p : p y notin Y_0} = 0`. Writing `p = (ma) n` and using `MA`-invariance of `Y_0`,
   this is `Haar_{MA} x Haar_N` of `MA x {n : n y notin Y_0}`, so the second factor is null.

By the correspondence of invariant sets, `Z_bad = {z : iota z notin S_good}` is `Gamma`-invariant and `mu`-null.

Fix `z notin Z_bad`, and let `theta = xi(z)`. Choose the section in the form `sigma(theta, theta') = s(theta) n(theta'')`
with `s(theta) eP = theta`, `theta'' = s(theta)^{-1} theta'`, and `n(theta'') in N` the unique element with
`n(theta'') wP = theta''` (R1). This is legitimate by Lemma 3.
- Then `y_1 = n(theta'')^{-1} y_z` with `y_z = s(theta)^{-1} iota(z) in Y ∩ S_good`, since `S_good` is `G`-invariant.
- The map `theta' ↦ n(theta'')` is a diffeomorphism from `dX \ {theta}` onto `N`. So `xi_*(mu) << Leb` makes
  `n(theta'')` `Haar_N`-absolutely continuous as `z'` ranges.
- By Lemma 4.2, `y_1 in Y_0` for `mu`-a.e. `z'`.

By Fubini the first condition of `D_F` holds `mu x mu`-a.e. The second holds by the symmetric argument, using the
section `sigma(theta, theta') = sigma'(theta', theta) w^{-1}`, which is allowed by Lemma 3. So `D'` is conull.

## Step 5: dissipation

`Gamma` is discrete, so it acts properly on `X`. For `(z,z') in D'` put
`Mfin(z,z') = {γ in Gamma : d(γ o, f(z,z')) <= d(f(z,z'), Gamma o) + 1}`. This set is finite and nonempty, and
`Mfin(γ z, γ z') = γ Mfin(z,z')`. By (R4) applied to `Z x Z` with `D = D'`, `Con(Z x Z)` is null. This proves the
Theorem.

**`G`-version.** For an imp `G`-space `W` with `pi : W -> dX`, run Steps 1--3 with `W` in place of `Zhat`. Lemma 4
holds verbatim. For `zhat in S_good`, the argument of Step 4 shows that `y_1 in Y_0` for every partner `zhat'` whose
boundary point lies outside a `Leb`-null set. By (R2), `pi(zhat')` is `Leb`-absolutely continuous as `zhat'` ranges
over `W`. Fubini makes `D_F` conull for `muhat x muhat`, and `Fhat` is a `G`-equivariant map `W x W -> X` on it.

## Step 6: corollaries

- **Restrictions.** If `W` is an amenable imp `G`-space, the Zimmer map `W -> Prob(dX)` together with Step 4 of
  `fpbs-hyperbolic-bb-criterion-obstruction-proof` (applied to `W|_Gamma` componentwise; a cocompact lattice is
  hyperbolic with `dGamma = dX`) gives, under PDR, a Dirac boundary map whose push-forward class is
  `G`-quasi-invariant, hence `Leb`. The Theorem contradicts PDR. A finite-measure extension has the same boundary
  class.
- **Maharam extensions.** For a quasi-invariant `nu_0 << Leb`, the Maharam extension `(dX x R, nu_0 x e^t dt)` has
  the boundary map `xi(eta,t) = eta`, and `xi_* mu` has the null ideal of `nu_0`, so it is `<< Leb`.
- **Reduction.** For an ergodic PDR amenable action of a cocompact lattice, item 4 of
  `fpbs-hyperbolic-bb-criterion-obstruction` gives `phi = delta_xi`. The Lebesgue decomposition of the class
  `xi_* mu` into absolutely continuous and singular parts is `Gamma`-invariant, because `Gamma` preserves the `Leb`
  class. Ergodicity leaves one part. If it is the absolutely continuous part, the Theorem kills PDR. So the class is
  singular. For non-ergodic actions, apply this to a.e. component (Bevilacqua--Bowen, Lemma `L:conserv-erg-dec`).

## Where the argument stops

For singular `xi_* mu`, Step 4 needs `Y_0` to contain `N`-orbit points `n y_z` for `n` in a Haar-null set
(the singular partner directions). The height `h` of Lemma 2 is built from occupation times of the scaling flow and
carries no regularity along `N`: backward `A`-orbits of `y` and `n y` diverge, since `a_{-t}` expands `N`. So the
construction gives no information off a Haar-null set. A proof for singular classes needs a height that is
`N`-regular, or a different smoothing of the class.
