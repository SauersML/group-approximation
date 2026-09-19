---
rg: 2
id: fpbs-ray-code-deaths-depend-only-on-the-current-proof
kind: route
title: Proof that the backward-locally-finite death of ray codes with a finite invariant measure is decided by atomicity and local finiteness of the conditionals of the invariant current, that this is an exact dichotomy, that the geodesic-flow Markov code of a cocompact Sp(n,1) lattice is quasiconvex-null and essentially accumulating, and that at zero entropy the forward word determines the past
target: fpbs-ray-code-deaths-depend-only-on-the-current
requires:
  - fpbs-backward-locally-finite-ray-codes-die
  - fpbs-dini-boundary-class-diagonal-dissipative
---

# Proof

Notation is as in the claim and in `fpbs-backward-locally-finite-ray-codes-die` (cited as [BLF]) and its proof. The
identity (0.1) of [BLF] is: for `t ∈ Z`, `(zeta^{-#}, zeta^#)((T^#)^t p) = P_p(t)^{-1} (zeta^{-#}(p), zeta^#(p))`.
`K_r(eta) = {theta : (theta|eta)_o <= r}`. Since `(.|.)_o` is continuous on `dGamma` up to `2 delta`,
`cl K_r(eta) ⊂ K_{r+2delta}(eta)`, which does not contain `eta`.

## Step 1. The current and its marginals

Let `m = rho^# x count` on `Y = X^# x Gamma`, `S(p, g) = (T^# p, g P_p(1))`, `h.(p, g) = (p, hg)` for `h ∈ Gamma`, and
`Phi(p, g) = g (zeta^{-#}(p), zeta^#(p))`.

**1.1.** `S` preserves `m` (`T^#` preserves `rho^#`, and for fixed `p` the map `g -> g P_p(1)` is a bijection of
`Gamma`), commutes with the `Gamma`-action, and `Phi ∘ S = Phi` by (0.1) with `t = 1`. `Phi` is `Gamma`-equivariant.

**1.2 (fundamental domain).** By (UQ), for each `(p, g)` the set of `t` with `|g P_p(t)|` minimal is finite and
nonempty. Let `D` be the set of `(p, g)` such that `t = 0` is the least such `t`. Every `S`-orbit meets `D` exactly
once, and `D` is Borel. So `Y = ⊔_{k ∈ Z} S^k D` and `m` is `S`-invariant.

**1.3 (independence and invariance).** If `D'` is another Borel fundamental domain and `F` is an `S`-invariant Borel
function, then `∫_D F dm = ∫_{D'} F dm`: cut `D = ⊔_k D ∩ S^k D'` and use `S^{-k}`-invariance of `m` and `F`. Apply
this to `F = 1_B ∘ Phi`: `mu_R := Phi_*(m|_D)` does not depend on `D`. Since `hD` is again a fundamental domain,
`h_* mu_R = Phi_*(m|_{hD}) = mu_R`. So `mu_R` is `Gamma`-invariant and carried by `Phi(Y) = R`.

**1.4 (Radon).** By [BLF] proof 1.2, if the geodesic between `Phi(p, g)` passes within `r` of `o`, the nearest vertex
`g` of the line `g P_p` lies in `Ball(o, r + M + C_1)`. So `mu_R` gives mass at most
`|Ball(o, r + M + C_1)| rho^#(X^#)` to the compact set of pairs whose geodesic meets `Ball(o, r)`, and these sets
exhaust `dGamma^2 \ Delta`.

**1.5 (marginal classes).** Let `pi_±` be the two coordinate projections. For `t ∈ Z` let
`E_t = {p : S^t(p, 1) ∈ D}`; these partition `X^#`. `S^t` maps `E_t x {1}` into `D`, and `Phi ∘ S^t = Phi`, so
`mu_R >= Phi_*(m|_{E_t x {1}})`, whose forward marginal is `zeta^#_*(rho^#|_{E_t})`. Summing over `t`,
`zeta^#_* rho^# << pi_{+*} mu_R`, and by invariance `g_* zeta^#_* rho^# << pi_{+*} mu_R` for all `g`. Conversely
`pi_{+*} mu_R = sum_g g_* zeta^#_*(rho^#|_{D_g})` with `D_g = {p : (p, g) ∈ D}`. So `pi_{+*} mu_R` (sigma-finite by
1.4 after restricting to the compact pieces) is equivalent to `nu`. The same argument with `pi_-` gives `nu^-`.

**1.6 (null sets of positions).** If `B ⊂ dGamma^2` is Borel, `Gamma`-invariant and `mu_R`-null, then
`rho^#{p : (zeta^{-#}(p), zeta^#(p)) ∈ B} = 0`. Indeed `W = Phi^{-1}(B)` is `S`- and `Gamma`-invariant, and
`m(W ∩ D) = mu_R(B) = 0`, so `m(W) = sum_k m(S^k(W ∩ D)) = 0`, and `W ⊃ {p : Phi(p, 1) ∈ B} x {1}`.

**1.7 (disintegration).** Choose a finite measure `nu_1 ~ pi_{+*} mu_R`. On each compact piece `Q_j` (pairs whose
geodesic meets `Ball(o, j)`) disintegrate the finite measure `mu_R|_{Q_j}` over `pi_+` with respect to `nu_1`; the
conditionals are compatible in `j` a.e., giving sigma-finite `mu^eta` on `dGamma \ {eta}` with
`mu_R = ∫ mu^eta d nu_1(eta)`, finite on `K_r(eta)` for all `r` (by [BLF] (Line), `K_r(eta) x {eta}` lies in some
`Q_j`). Uniqueness of disintegration and `g_* mu_R = mu_R` give, for each `g`, `mu^{g eta} = c_g(eta) g_* mu^eta`
with `c_g(eta) > 0`, for `nu`-a.e. `eta`. Since `Gamma` is countable there is a `Gamma`-invariant `nu`-conull Borel
set `G_0` on which all these relations hold and on which the conditionals are defined.

## Step 2. Proof of Theorem 1

Let `A = {(theta, eta) : eta ∈ G_0, mu^eta({theta}) > 0}`, the set of atoms.

*Borel.* For a refining sequence of finite Borel partitions `{Q_{k,i}}` of `dGamma` with mesh `-> 0`,
`mu^eta|_{K_r}({theta}) = lim_k mu^eta(K_r(eta) ∩ Q_{k,i(theta)})`, a Borel function of `(theta, eta)`; take the
union over `r`.

*Invariant.* On `G_0`, `mu^{g eta}` is a positive multiple of `g_* mu^eta`, so `theta` is an atom of `mu^eta` iff
`g theta` is an atom of `mu^{g eta}`: `gA = A`.

*Conull.* By (LF_mu), `mu^eta(dGamma \ A^eta) = 0` for `nu`-a.e. `eta`, so `mu_R(dGamma^2 \ A) = 0`.

*The restriction.* Let `X_1 = {x ∈ X_0 : (zeta^-(x), zeta(x)) ∈ A}`. By (0.1) and `gA = A`, the pair of every position
over the `T`-orbit of `x` is a `Gamma`-translate of that of `x`; hence `X_1` is `T`-invariant and
`X_1^# = {p : (zeta^{-#}(p), zeta^#(p)) ∈ A}`. By 1.6 applied to `B = dGamma^2 \ A`, `rho^#(X^# \ X_1^#) = 0`. The
restricted code has code relation `R_1 = Gamma . {(zeta^-(x), zeta(x)) : x ∈ X_1} ⊂ A` and, since `rho^#` is carried by
`X_1^#`, the same class `nu`.

*(LF) for `R_1`.* For `nu`-a.e. `eta`, `R_1^eta ⊂ A^eta`, the set of atoms of `mu^eta`, which by (LF_mu) meets each
`K_r(eta)` in a finite set. This is (LF) of [BLF].

*(NF) for `R_1`.* Suppose `nu((R_1)_theta) > 0` for some `theta`. Since `(R_1)_theta ⊂ A_theta = {eta ∈ G_0 :
mu^eta({theta}) > 0}`, we get `mu_R({theta} x dGamma) >= ∫_{A_theta} mu^eta({theta}) d nu_1(eta) > 0`, because
`nu_1 ~ nu` and the integrand is positive on `A_theta`. Then `pi_{-*} mu_R` has an atom at `theta`, and by 1.5 so does
`nu^-`, contrary to hypothesis. So `nu((R_1)_theta) = 0` for every `theta`.

*Conclusion.* [BLF] Theorem 1 with its restriction clause, applied to the code on `X_1`, gives total dissipativity of
the diagonal of every imp `Z` with `xi_*(mu_Z|_E) << nu`, and no ergodic such `Z` is PDR. `□`

## Step 3. Proof of Corollary 2

If (LF_mu) holds, Theorem 1 applies. Suppose (LF_mu) fails on a `nu`-positive set `U`, and let `X_1` be any conull
`T`-invariant Borel set with relation `R_1`. The set `Gamma . {(zeta^-(x), zeta(x)) : x ∈ X_0 \ X_1}` need not be
Borel, so argue on positions: `W = {(p, g) : p ∉ X_1^#}` is `S`- and `Gamma`-invariant and `m`-null, so
`mu_R(Phi(D \ W)^c) <= m(D ∩ W) = 0`, i.e. `mu_R` is carried by the analytic set `Phi(D \ W) ⊂ R_1`. Hence for
`nu`-a.e. `eta`, `mu^eta` is carried by `R_1^eta` (analytic sets are universally measurable). For `eta ∈ U` outside
this null set, some `K_r(eta)` carries either a nonatomic part of `mu^eta` or infinitely many atoms. In the first case
`R_1^eta ∩ K_r(eta)` is uncountable (a countable set is null for a nonatomic measure); in the second it contains the
infinitely many atoms. Either way it is infinite, so it has an accumulation point `theta ∈ cl K_r(eta)`, and
`theta ≠ eta` by the remark at the top. `□`

## Step 4. Proof of Theorem 3 (the geodesic-flow Markov code)

Let `H` be quaternionic hyperbolic space of real dimension `4n`, `Gamma` a cocompact lattice, and (Selberg) `Gamma_0`
a torsion-free normal subgroup of finite index, so `M = Gamma_0 \ H` is a compact manifold with pinched negative
curvature and `dGamma = dH = S^{4n-1}`. Fix `õ ∈ H` and a Borel fundamental domain `F ∋ õ` for `Gamma_0` with compact
closure. Metrics on `Gamma_0` and on `Gamma_0 õ` are quasi-isometric (Švarc--Milnor).

**4.1 (the code).** The geodesic flow `phi_t` on `T^1 M` is Anosov. By Bowen (Amer. J. Math. 95 (1973)) it has a
Markov family of rectangles with cross-section `Sigma`, first-return map `T_Sigma` and return time `tau` with
`0 < tau_min <= tau <= tau_max`, and a Hölder surjection `pi : Sigma_A -> Sigma` from a mixing SFT with
`pi ∘ sigma = T_Sigma ∘ pi`, injective off the preimage of the `phi`-orbits of the rectangle boundaries. The Liouville
measure `m_L` is the equilibrium state of a Hölder potential, so it gives that boundary set measure zero, and it
induces a `T_Sigma`-invariant ergodic probability on `Sigma`; let `rho` be its lift to `Sigma_A`. It is nonatomic, so
the set `X_0` of `sigma`-aperiodic points is conull and invariant.

For `x ∈ X_0` let `ṽ(x)` be the lift of `pi(x)` with footpoint in `F` (Borel in `x`), and `gamma_x` its geodesic.
There is a unique `G_1(x) ∈ Gamma_0` with `phi_{tau(x)} ṽ(x) = G_1(x) ṽ(sigma x)`. Put
`P_x(j) = G_1(x) G_1(sigma x) ... G_1(sigma^{j-1} x)` (and the inverse products for `j < 0`). Then
`phi_{tau_j(x)} ṽ(x) = P_x(j) ṽ(sigma^j x)` with `tau_j = sum_{i<j} tau(sigma^i x) ∈ [j tau_min, j tau_max]` for
`j >= 0`, so `d(P_x(j) õ, gamma_x(tau_j)) <= diam F`, and likewise for `j < 0`. Fix `k` with
`k tau_min > 2 diam F + 1` and use `T = sigma^k` with letters `G(x) = P_x(k)`: `d(õ, G(x) õ) >= k tau_min - 2 diam F > 0`,
so `G(x) ≠ 1`, and `G` takes finitely many values. Spell each letter by a fixed geodesic `S_0`-word. `T` is aperiodic on
`X_0` and preserves `rho`.

**4.2 ((UQ) and endpoints).** The letter-boundary path is `j -> P_x(kj)`, which stays within `diam F` of
`gamma_x(tau_{kj})`, with `tau_{kj}` between `kj tau_min` and `kj tau_max`. Letters have bounded length, so the refined
paths are uniformly quasi-geodesic in `Gamma_0` (constants from `tau_min, tau_max, k, diam F` and Švarc--Milnor),
and `zeta^±(x) = gamma_x(±∞)`. As a code on `Gamma`, take `S ⊃ S_0`; as in [BLF] Step 6 item 1--2, (UQ) persists, the
relation is `R = ⋃_i k_i R_0` over coset representatives, and the class is `sum_i (k_i)_* nu_0`.

**4.3 (the relation).** Let `(theta, eta) ∈ dH^2 \ Delta` with geodesic `gamma`. Its image orbit in `T^1 M` meets
`Sigma` at some `v = pi(x)`, `x ∈ Sigma_A`. If `x` is `sigma`-periodic then `v` is `T_Sigma`-periodic, the orbit is
closed, and `{theta, eta}` is the fixed pair of a loxodromic element of `Gamma_0`. Otherwise `x ∈ X_0`, and `gamma`
passes through a lift `g ṽ(x)`, `g ∈ Gamma_0`, so `(theta, eta) = g (zeta^-(x), zeta(x)) ∈ R_0` (the `sigma^k`-line
through `x` has the same endpoints). So `R_0 ⊃ dH^2 \ (Delta ∪ Fix)`, `Fix` the countable set of loxodromic fixed
pairs, and `R^eta ⊃ dH \ {eta}` minus a countable set for every `eta`.

**4.4 (the class).** `zeta_* rho` is the image of the section measure of `m_L` under the forward endpoint map. In
Hopf coordinates `T^1 H = dH^2 \ Delta x R`, the lift of `m_L` is equivalent to `Leb x Leb x dt`. Hence the forward
code class is the Lebesgue class `[Leb]`, and so is the backward class. Both are nonatomic. `[Leb]` is `Gamma`-ergodic
(Moore ergodicity for the lattice `Gamma < Sp(n,1)` acting on `G/P`).

**4.5 (quasiconvex-null).** Let `L <= Gamma` be quasiconvex of infinite index. Its limit set is uniformly conical, so
its Hausdorff dimension for the visual (Carnot--Carathéodory) metric equals the critical exponent `delta_L`
(Coornaert, Pacific J. Math. 159 (1993)). By Dahmani--Futer--Wise (Math. Proc. Cambridge 167 (2019)), infinite-index
quasiconvex subgroups of a hyperbolic group have strictly smaller growth rate: `delta_L < delta_Gamma = 4n + 2`. Lebesgue
measure is Ahlfors `(4n+2)`-regular for this metric, so `Leb(g Lambda_L) = Leb(Lambda_{g L g^{-1}}) = 0`.

**4.6 (the current).** Let `B ⊂ dH^2 \ Delta` be Borel and `Gamma_0`-invariant. By 1.5 and 1.6 (for the code on
`Gamma_0`), `mu_{R_0}(B) = 0` iff `rho{x : (zeta^-(x), zeta(x)) ∈ B} = 0`. The set of `v ∈ T^1 M` whose lifts have
endpoint pair in `B` is `phi`-invariant, so it is `m_L`-null iff its section trace is null, iff the last condition
holds; and by 4.4 it is `m_L`-null iff `(Leb x Leb)(B) = 0`. For arbitrary Borel `B`, both `mu_{R_0}` and `Leb x Leb` are
`Gamma_0`-quasi-invariant, so `B` is null for either iff `Gamma_0 B` is. Hence `mu_{R_0} ~ Leb x Leb`, and the current on
`Gamma`, `sum_i (k_i)_* mu_{R_0}`, is also equivalent to `Leb x Leb`, that is to the Liouville current.

**4.7 (accumulation and death).** Equivalent measures have a.e. equivalent conditionals. The conditionals of
`Leb x Leb` over the forward coordinate are `Leb` on `dH \ {eta}`. So for `nu`-a.e. `eta`, `mu^eta ~ Leb`, which is
nonatomic: (LF_mu) fails a.e. and, by Corollary 2, every conull restriction has accumulating backward sections at
`nu`-a.e. point. Lebesgue measure on `S^{4n-1}` is Ahlfors regular of positive dimension, so its modulus satisfies
`omega(r) <= C r^alpha` and it is Dini. By Theorem B of `fpbs-dini-boundary-class-diagonal-dissipative`, every imp
action with a boundary map into `[Leb]` has totally dissipative crossing diagonal and no ergodic one is PDR. Nothing
in this uses `R`. `□`

(The same proof applies to every Gibbs measure of a Hölder potential in place of `m_L`: the current is then
equivalent to a product of two Gibbs boundary classes, and those classes have positive dimension. So every
equilibrium-state code of the geodesic flow is essentially accumulating and dies by size.)

## Step 5. Proof of Proposition 4

Normalize `rho^#` to a probability. The letter process `a_j(p) = P_p(j)^{-1} P_p(j+1) = s_1((T^#)^j p) ∈ S` is a
stationary finite-valued process, a factor of `(X^#, T^#, rho^#)`, so it has entropy `0`. For a stationary
finite-valued process the entropy equals `H(a_0 | a_1, a_2, ...)` (the reversed process has the same entropy), so
`a_0` is measurable, mod `rho^#`, with respect to `sigma(a_1, a_2, ...)`. By stationarity `a_{-k}` is measurable with
respect to `sigma(a_{-k+1}, a_{-k+2}, ...)` for each `k >= 1`, and by induction every `a_{-k}` is measurable with
respect to `F^+ = sigma(a_0, a_1, ...)`, the forward `S`-word. The backward path is
`P_p(-t) = (a_{-t} ... a_{-1})^{-1}`, so `zeta^{-#}(p) = lim_t P_p(-t)` equals `Psi(w(p))` for a Borel `Psi` of the forward
word `w(p)`, off a `rho^#`-null set.

By 1.3--1.5, `mu_R = sum_g g_* (Psi ∘ w, zeta^#)_*(rho^#|_{D_g})`. Disintegrating `rho^#|_{D_g}` over `zeta^#` gives
the stated description of `mu^eta` as a sum over the finitely many `g` with `(p, g) ∈ D` and `g zeta^#(p)` near a
given `K_r`-piece, of images under `w -> g Psi(w)` of conditional laws of forward words with endpoint `g^{-1} eta`.
In the respelled codes of [BLF] Theorem 3, the forward words over one base point `x` all have the same group path at
letter boundaries, hence the same past endpoint `Psi(w)`, so the respelling contributes nothing to `mu^eta`. `□`

## Step 6. Proof of Corollary 5

Let `Z` be an ergodic amenable PDR imp action with `xi_*(mu_Z|_E) << nu` for every finite-measure `E`. By
Theorem 1 and Corollary 2, if the current were not essentially accumulating, the diagonal would be totally dissipative
and `Z` not PDR. So it is essentially accumulating. The boundary class `C = [xi_* mu_Z]` is `Gamma`-quasi-invariant
and ergodic, since `Z` is ergodic. By Theorem C of `fpbs-dini-boundary-class-diagonal-dissipative`, `C` is either
absolutely continuous with respect to one finite Dini measure, in which case Theorem B there makes `Z` non-PDR, or
singular to every Dini measure, and then every measure in `C` has lower local dimension `0` a.e. (the contrapositive
of the last sentence of Theorem C). Theorem 3 exhibits a quasiconvex-null code with essential accumulation whose class
is Dini; so neither condition of the corollary follows from quasiconvex-nullness together with the other. `□`

## Remarks

**Remark 6.1 (why the Borel--Cantelli test against `mu_R` cannot close the route).** A count of lines through a ball
against the Radon bound 1.4 controls the *total* mass of the backward conditionals on `K_r(eta)`, not their atomic
structure. The Liouville current has finite mass on every `K_r(eta)` and nonatomic conditionals, and its class is
quasiconvex-null (4.5). So no argument that uses only Radon-ness of the current, `Gamma`-invariance and
quasiconvex-nullness of the class can force (LF_mu). Any closure of the ray-code route must use Dini-singularity (or
the dimension-zero consequence of zero entropy, [BLF] Proposition 4) together with the current.

**Remark 6.2 (the zero-entropy test).** At zero entropy, Proposition 4 turns essential accumulation into a statement
about the fibres of the forward-word map over endpoints: a nonatomic conditional family of forward words with a common
endpoint on which the past endpoint `Psi` is non-constant. Right-asymptotic pairs of a zero-entropy subshift (which
exist in every infinite expansive system) are the natural source: a right ray with infinitely many left extensions
whose group paths diverge in the past. Whether such a family can be nonatomic under a quasi-geodesic, quasiconvex-null
coding with a conservative diagonal is the concrete open question.
