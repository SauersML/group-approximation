# Weakly Bernoulli liftable actions and the norm of the extension class (part 1)

Lane ex2-rokhlin-almost-cocycle, 2026-09-13. Target: `weakly-bernoulli-liftable-actions-force-virtual-splitting`,
negative direction. Unreviewed. The engine is Gohla--Thom's metric cohomology; what is new here is small and is
flagged as such in Section 6.

## 0. Setting

- `Gamma` countable of type F (a finite model `BGamma`), `A` finite abelian, `alpha in H^2(Gamma, A)` classifying a
  central extension `1 -> A -> Gamma~ -> Gamma -> 1`. `alpha_0` is a fixed cocycle on the cells of `BGamma`.
- For a p.m.p. action `Z` with measure algebra `P = M(Z)`, `P(A) = L^0(Z, A)`. Gohla--Thom define
  `theta_*^Z : H^2(Gamma, A) -> H^2(Gamma, P(A))` and a pseudo-norm `|||.|||` on `H^2(Gamma, P(A))`, the quotient of
  the cochain length `||c|| = sum over 2-cells x of mu(c(x)) nu(x)`, where `mu(c(x))` is the measure of the set where
  `c(x) != 0`. It depends on the model and the weights only up to bi-Lipschitz equivalence, so `|||.||| = 0` and
  `|||.||| > 0` are properties of `Gamma`.
- `Z` is **liftable** if `Z = X/A` for a free p.m.p. `Gamma~`-action `X`.
- `Bern = [0,1]^Gamma`. All nontrivial Bernoulli shifts of `Gamma` are weakly equivalent: each is free, so each is
  weakly contained in every other by Abert--Weiss.
- Torsion: if `Gamma` has torsion (e.g. `Sp_4(Z)`), pass to a torsionfree finite-index `Gamma'` (e.g. level 3).
  Restriction preserves liftability and weak containment, and `Bern(Gamma)|Gamma'` is a Bernoulli shift of
  `Gamma'`. So the target over `Gamma'` implies it over `Gamma`.

## 1. Imports, quoted from Gohla--Thom, arXiv:2403.09582v2 (PDF read 2026-09-13)

**Definition 2.2.** "We say that a measured Γ-Boolean algebra (P, μ) is weakly contained in a family of measured
Γ-Boolean algebras if (P, μ) is contained in a metric ultraproduct of measured Γ-Boolean algebras from that family."
(They add that this "corresponds to the notion of weak containment of measure preserving actions".)

**Definition 2.8 (i).** Γ satisfies "a cosystolic inequality in dimension i with respect to 𝒫 and A, if there exists
ε > 0, such that |||α|||_i ≥ ε for all non-zero α ∈ H^i(BΓ, P(A)) and all (P, μ) ∈ 𝒫".

**Theorem 2.10.** "Let d ≥ 4 and p large enough. Let Γ be a torsionfree lattice in PSp_2d(Q_p) and let A be a
finite abelian group. Then, Γ satisfies a cosystolic inequality and expansion with respect to the family of finite
transitive Γ-actions and A in dimensions 0 ≤ i ≤ d − 2."

**Lemma 2.13.** "Let Γ be of finite type, 𝒫 be a family of measured Γ-Boolean algebras and A be an abelian group.
Let (P_j, μ_j)_{j∈I} be an indexed set of elements of 𝒫 and 𝒰 ∈ βI be a non-principal ultrafilter. Then, the
natural map H^i_red(Γ, P_j(A))_𝒰 → H^i_red(Γ, P_𝒰(A)) is an isometric injection and it is surjective if Γ satisfies
expansion in dimension i with respect to the family 𝒫 and A. In particular, we have
|||θ_*^{P_𝒰}(α)|||_{μ_𝒰} = lim_{j→𝒰} |||θ_*^{P_j}(α)|||_{μ_j} for all α ∈ H^i(Γ, A)."
The isometry (first half of its proof) uses no expansion.

**Corollary 2.14.** "Let Γ be a group of finite type, let (P, μ) be a measured Γ-Boolean algebra and let 𝒫 be a
family of measured Γ-Boolean algebra. If |||θ_*^P(α)|||_μ < inf{|||θ_*^Q(α)|||_ν | (Q, ν) ∈ 𝒫} for some
α ∈ H^i(Γ, A), then (P, μ) is not weakly contained in the family 𝒫." Its proof shows: if P is contained in
P_𝒰, then "the natural map H^i(Γ, P(A)) → H^i(Γ, P_𝒰(A)) is contractive and hence |||θ_*^P(α)|||_μ ≥
|||θ_*^{P_𝒰}(α)|||_{μ_𝒰} = lim_{j→𝒰} |||θ_*^{P_j}(α)|||_{μ_j}".

**Theorem 2.16.** "Let A be a finite abelian group. Let Γ be a residually finite group which satisfies a co-systolic
inequality in dimension 2 for all finite transitive actions with respect to A. If α ∈ H^2(Γ, A) classifies a
central extension Γ~ which is not residually finite, then 0 ≠ θ_*^P(α) ∈ H^2(Γ, P(A)) whenever the measured
Γ-Boolean algebra P is weakly contained in the family of finite actions. In particular, this holds for P = M(Γ^)."
Its proof gives a uniform lower bound on |||θ_*^Q(α)||| over all finite actions Q, then applies Corollary 2.14.

**Theorem 3.4.** "Let Γ~ be a central extension of Γ by the finite abelian group A and let α ∈ H^2(Γ, A) be the
cohomology class that classifies this extension. Let (Q, μ) be an A-free measured Γ~-Boolean algebra and let
P := Q^A be the subalgebra of A-invariants. Then, 0 = θ_*^P(α) ∈ H^2(Γ, P(A))."

**Theorem 3.18** (following Deligne). "Let p ≥ 5 and A the cyclic group of order p − 1. For the torsion-free lattice
Γ ≤ PSp_2d(Q_p) discussed above, the central extension 0 → A → Γ~ → Γ → 0 is not residually finite." Here Γ is a
torsionfree finite-index subgroup of G(Z[1/p]), with G = SU_d(D, h_d) of type C_d, and Γ~ is the pullback of
Prasad's universal central extension. Section 3.4 of the paper: "taking p large enough in order to allow for the
application of Theorem 2.10, we see that all conditions in Theorem 3.13 are met."

**Remark 3.14** (the Bernoulli-quotient case). "the Bernoulli action Γ ↷ ({0,1}^Γ, ν^{⊗Γ}) is weakly contained in
any other free p.m.p. action. In particular, since Γ is residually finite, it is weakly contained in the pro-finite
action Γ ↷ (Γ^, μ_Haar). Hence, θ_*^{M({0,1}^Γ, ν^{⊗Γ})}(α) ≠ 0 by Theorem 2.16. On the other side, we have
θ_*^{M(X,μ)}(α) = 0 for Γ ↷ X = {0,1}^{Γ~}/A ... by Theorem 3.4. In particular, Γ ↷ X = {0,1}^{Γ~}/A is not weakly
contained in the family of finite actions of Γ."

## 2. Liftable means exactly `theta_*^Z(alpha) = 0`

**Lemma L.** For a free p.m.p. `Gamma`-action `Z`: `Z` is liftable iff `theta_*^Z(alpha) = 0`.

*Proof.* (=>) Theorem 3.4 with `Q = M(X)`. Directly: choose a Borel section `s : Z -> X`. For `g in Gamma` and a
set-theoretic lift `g~`, `g~ s(z) = s(gz) + b(g, gz)` with `b(g, .) in L^0(Z, A)`, since `A` acts freely. Then
`alpha_0 = delta b` in inhomogeneous cochains, so `theta_*^Z(alpha) = 0`. Cellular `H^2(BGamma, M)` and group
cohomology `H^2(Gamma, M)` both compute `Ext^2_{ZGamma}(Z, M)`, so this vanishing is the vanishing in Gohla--Thom's group.
(<=) Suppose `alpha_0(g, h) = g.beta_h - beta_{gh} + beta_g` with `beta_g in L^0(Z, A)` and `(g.f)(z) = f(g^-1 z)`.
Realize `Gamma~ = Gamma x A` with `(g,a)(h,b) = (gh, a + b + alpha_0(g,h))`, and set
`T_(g,a)(z, t) = (gz, t + a + beta_g(gz))`. Then `T_(g,a) T_(h,b)(z,t) = (ghz, t + a + b + beta_h(hz) + beta_g(ghz))`.
With `w = ghz`, `beta_h(hz) + beta_g(w) = (g.beta_h)(w) + beta_g(w) = alpha_0(g,h) + beta_{gh}(w)`, so this equals
`T_(gh, a+b+alpha_0(g,h))(z,t)`. It is an action, it preserves `mu x counting/|A|`, `A` acts by free translation,
the quotient is `Z`, and the action is free because `Z` is free. QED

## 3. The norm can only drop under weak containment

**Lemma M.** If `Z ≺ Z'` (weak containment of p.m.p. actions), then `|||theta_*^Z(alpha)||| >= |||theta_*^{Z'}(alpha)|||`.

*Proof.* By Definition 2.2, `M(Z)` is contained in an ultrapower `M(Z')_𝒰`. The proof of Corollary 2.14 gives
`|||theta^Z||| >= |||theta^{M(Z')_𝒰}||| = lim_𝒰 |||theta^{Z'}||| = |||theta^{Z'}|||`, by the isometric half of Lemma 2.13 for
the constant family `P_j = M(Z')`. QED

## 4. Theorem N: Bernoulli maximizes the norm, and the norm decides weakly Bernoulli lifts

**Theorem N.** Let `Gamma` be of type F and `alpha in H^2(Gamma, A)`.
- (a) `|||theta_*^Z(alpha)||| <= |||theta_*^Bern(alpha)|||` for every free p.m.p. `Gamma`-action `Z`.
- (b) Some liftable free action is weakly contained in `Bern` iff `|||theta_*^Bern(alpha)||| = 0`.
- (c) So "no liftable free action is weakly contained in `Bern`" holds iff `|||theta_*^Z(alpha)||| > 0` for some free
  action `Z`.

*Proof.* (a) Abert--Weiss gives `Bern ≺ Z`; apply Lemma M.
(b) (=>) If `Y` is liftable and `Y ≺ Bern`, Lemma L and Lemma M give `0 = |||theta^Y||| >= |||theta^Bern|||`.
(<=) Take cocycle representatives `c_n = theta(alpha_0) + delta zeta_n` with `||c_n|| -> 0`. In the ultrapower
`P_𝒰 = M(Bern)_𝒰`, `[c_n]_𝒰 = 0`, because there are finitely many 2-cells and each weight is positive. So
`theta(alpha_0) = -delta zeta` with `zeta = [zeta_n]_𝒰`. This cochain is equivariant, so finitely many elements of
`P_𝒰(A)` determine it, one per `Gamma`-orbit of 1-cells. Let `P` be the smallest closed invariant subalgebra of
`P_𝒰` containing the diagonal copy of `M(Bern)` and the level sets of those elements. `P` is separable. By
Mackey's point realization, `P = M(Y)` for a p.m.p. `Gamma`-action `Y` on a standard space. `Y` has `Bern` as a
factor, so it is free. `theta^Y(alpha) = 0` because `zeta` has values in `P(A)`, so `Y` is liftable by Lemma L.
`P ⊂ P_𝒰` gives `Y ≺ Bern`.
(c) follows from (a) and (b), since `Bern` is free. QED

**Unpacked.** `|||theta^Bern(alpha)||| = 0` means: for every `eps > 0` there are measurable `b : (1-cells) x Bern -> A`
whose twisted coboundary differs from `alpha_0` on a set of measure `< eps` at every 2-cell. This is the
almost-cocycle formulation in the target's body, now as a normed cohomology statement with an exact converse.

## 5. Theorem G: the target claim holds over the Gohla--Thom lattices

**Theorem G.** Let `d >= 4` and `p >= 5` be large enough for Theorem 2.10, `Gamma` and `Gamma~` as in Theorem 3.18,
and `A = Z/(p-1)`. There is `eps_0 > 0` with `|||theta_*^Z(alpha)||| >= eps_0` for every p.m.p. `Gamma`-action `Z` weakly
contained in the family of finite `Gamma`-actions, including `Z = Bern`. So no liftable free `Gamma`-action is weakly
contained in `Bern`, or even in the finite actions. `Gamma` has property (T), and `Gamma~` is not virtually split.

*Proof.*
- **Hypotheses.** `Gamma` is residually finite (Malcev, GT Section 3.4) and of type F (GT Lemma 2.7). By Theorem 2.10
  (with `d - 2 >= 2`) it satisfies a cosystolic inequality in dimension 2 for finite transitive actions. By Theorem
  3.18, `Gamma~` is not residually finite.
- **Lower bound on finite actions.** On a finite transitive action `Gamma/Λ`, `theta^{Gamma/Λ}(alpha) != 0` by GT Lemma
  2.15, so its norm is at least `eps` by Definition 2.8(i). The length of a cochain on a disjoint union is the
  weighted average over the pieces, and coboundaries act piecewise. So every finite action has norm `>= eps =: eps_0`.
- **Weak containment.** The proof of Corollary 2.14 gives `|||theta^Z||| >= eps_0` whenever `Z` is weakly contained
  in the finite actions.
- **Bernoulli.** `Bern ≺ Γ^` by Abert--Weiss, because the translation action on the profinite completion is free.
  `M(Γ^)` is the closure of the increasing union of the finite invariant algebras `P^{Gamma/Λ_n}` along a descending
  chain of finite-index normal subgroups with trivial intersection. The diagonal map into `prod_𝒰 P^{Gamma/Λ_n}` is
  an equivariant, measure-preserving embedding. So `Bern` is weakly contained in the finite actions.
- **Liftable actions.** Lemma L excludes all of them.
- **Property (T).** `Gamma` is a lattice in `PSp_2d(Q_p)`, which has `Q_p`-rank `d >= 2`, so it has (T) and is
  w-rigid.
- **Not virtually split.** Splitting over a finite-index `Λ` would give `pi^-1(Λ) ≅ Λ x A`, which is residually
  finite, so `Gamma~` would be residually finite. QED

## 6. What is new, and where Popa stands

- **Credit.** For the single quotient `{0,1}^{Gamma~}/A`, Theorem G is GT Remark 3.14. Extending it to every liftable
  action needs only their Theorem 3.4 as stated. So Theorem G is a direct corollary of Gohla--Thom; this lane's
  contribution is to read it as the target claim over a property (T) base.
- **Not in GT.** Theorem N(a), that `Bern` maximizes the norm among free actions, is not stated there. Neither is the
  converse N(b)(<=). Both are short.
- **Unreduced versus reduced.** Popa (`bernoulli-lifts-across-finite-kernels-force-virtual-splitting`) gives
  `theta^Bern(alpha) != 0` in `H^2` for w-rigid `Gamma` and a non-virtually-split class. By Theorem N the target is
  the stronger statement `theta^Bern(alpha) notin NH^2`, meaning nonzero in reduced cohomology. Popa's proof does not
  give this. An ultrapower cocycle is not equicontinuous under the malleable deformation `alpha_t^𝒰`, so the (T) step
  "`alpha_t(w) -> w` uniformly" has nothing to start from.
- **Sp_4(Z).** For `Sp_4(Z)` with Deligne's class, no cosystolic inequality is known. It is a real lattice of rank 2,
  and GT Theorem 2.10 is Bruhat--Tits geometry. Part 2 treats this instance.

## 7. Model tests

- **Theorem N, hypothesis side.** Take `Gamma = Z^2`, `A = Z/3`, and `alpha` the mod-3 Heisenberg class.
  - `alpha` vanishes on `3Z^2`. Inducing `Bern(3Z^2) x A` from `3Z^2 x A` gives a free liftable action.
  - `Z^2` is amenable, so that action is weakly equivalent to `Bern`, and (b) gives norm 0 although `alpha != 0`.
  - So the norm separates "virtually split" from "nonzero".
- **Theorem G, conclusion side.** `{0,1}^{Gamma~}/A` is liftable, so its norm is 0. By Theorem G it is not weakly
  contained in the finite actions, which is GT Remark 3.14.
- **Trivial model.** For `alpha = 0` the norm is 0 and `Gamma~ = Gamma x A` is residually finite, so Theorem G's
  hypothesis fails, as it should.
