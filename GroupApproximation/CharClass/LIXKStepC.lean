import GroupApproximation.CharClass.LIXKCount
import GroupApproximation.CharClass.ThomStepCEuler
import GroupApproximation.Meta.AxiomGuard

/-!
# Step C's odd side with `k` zeros, abstractly

Lane `sp-oddside` of the STW Problem LIX strengthening
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.3.4; `sp-design`'s report §4.2).

## The structural finding

The `k`-zero Step C is **the one-zero Step C at a single chosen zero, plus the count**.
Nothing else is needed, and in particular the `k`-point punctured vanishing
`H^{2r}(N ∖ Z; F₂) = 0` is *not* on the critical path of this route.  The reason is that
the identification `γ_r = j(σ^* u)` comes from the naturality square
(`topClass_eq_of_naturality'`), which never uses surjectivity of `j`; so `j` on the
`k`-punctured pair is used only to receive the count, and the only place a group has to be
a line — hence the only place punctured acyclicity is consumed — is at the *distinguished*
zero `z_{i₀}`, where the existing `topChernClass_ne_zero_of_su_ne_zero_line` applies
character for character.

Concretely, with `c` the common value of the local classes:

* `c ≠ 0` is `ThomStepCEuler.topChernClass_ne_zero_of_su_ne_zero_line` at `z_{i₀}`, i.e.
  the mod-2 program's own Step C with `gamma := c`, `j := j_{i₀}`, `su := x_{i₀}`;
* `γ_r = j(x) = k · c ≠ 0` is `LIXKCount.map_ne_zero_of_localSplit`.

`CharClass/LIXKPunctured.lean` proves the `k`-point vanishing anyway — it is cheap, it is
what `sp-design` §4.2 item 1 asks for, and it is what makes `j` on the `k`-punctured pair
surjective, which any *other* arrangement of the argument would need.  It is simply not
consumed here.

## What is still open, and who owes it

Two of the seven binders below are the `k`-zero content and neither is discharged in this
file; both are named `Prop`s in `CharClass/LIXKCount.lean` with their owners in the
docstrings.

* `LocalSplit` — excision to `k` disjoint balls.
* `LocalClassesAgree` — `sp-design` §4.1's Half A and Half B.

The rest — `hacyclic`, `hexact`, `absLine`, `exc`, `chartIso`, `hx` — are the one-zero
Step C's own binders, at the distinguished zero, and are supplied by the existing tree.

## Main declarations

* `topChernClass_ne_zero_kzero` — the count, with `c ≠ 0` derived from the one-zero engine.
* `topChernClass_ne_zero_kzero_naturality` — the same with `γ_r` pinned to the Thom class
  through the section, which is the shape `LIXStepCOddWired` uses at one zero.
-/

noncomputable section

namespace GroupApproximation.CharClass

open CategoryTheory Limits
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

variable {N : Type} [TopologicalSpace N] {twoR : ℕ} {z₀ : N}

/-- **Step C's odd side with `k` zeros.**

`i₀` is the distinguished zero: the one at which the one-zero argument is run.  `hsplit`
and `hloc` are the two `k`-zero obligations; every other binder is the one-zero Step C's,
instantiated at `z₀`. -/
theorem topChernClass_ne_zero_kzero (hacyclic : PuncturedAcyclic N twoR z₀)
    {rel chart : ModuleCat.{0} (ZMod 2)} {r k : ℕ} (i₀ : Fin k)
    {relLoc : Fin k → ModuleCat.{0} (ZMod 2)}
    (j : rel ⟶ cohomologyZMod2 (TopCat.of N) twoR)
    (rho : ∀ i, relLoc i ⟶ rel)
    (jloc : ∀ i, relLoc i ⟶ cohomologyZMod2 (TopCat.of N) twoR)
    (hcompat : ∀ i, rho i ≫ j = jloc i)
    (ires : cohomologyZMod2 (TopCat.of N) twoR ⟶
      cohomologyZMod2 (TopCat.of ↥({z₀}ᶜ : Set N)) twoR)
    (hexact : LinearMap.range (jloc i₀).hom = LinearMap.ker ires.hom)
    (absLine : Nonempty (cohomologyZMod2 (TopCat.of N) twoR ≃ₗ[ZMod 2] ZMod 2))
    (exc : relLoc i₀ ≅ chart)
    (chartIso : chart ≅
      relCohomology (ZMod 2) (TopCat.of (Fin r → ℂ)) (puncturedSet r) (2 * r))
    {x : rel} {xloc : ∀ i, relLoc i} (hsplit : LocalSplit rho x xloc)
    (hx : xloc i₀ ≠ 0)
    {c : cohomologyZMod2 (TopCat.of N) twoR} (hloc : LocalClassesAgree jloc xloc c)
    (hk : ((k : ℕ) : ZMod 2) ≠ 0) :
    j.hom x ≠ 0 := by
  have hl : ∀ i, (jloc i).hom (xloc i) = c := hloc
  exact map_ne_zero_of_localSplit j rho jloc hcompat hsplit hloc
    (topChernClass_ne_zero_of_su_ne_zero_line hacyclic (jloc i₀) ires hexact absLine exc
      chartIso hx (hl i₀).symm)
    hk

/-- **The same, with `γ_r` pinned to the Thom class through the section.**  The naturality
square and the splitting of `σ^*` by `π^*` give `γ_r = j(σ^* u)`, so the conclusion is
about the top Chern class rather than about an anonymous element of the relative group.

This is the `k`-zero analogue of `ThomStepCOdd.topChernClass_ne_zero_odd`; note that the
naturality square is what makes the punctured acyclicity of the `k`-punctured base
unnecessary. -/
theorem topChernClass_ne_zero_kzero_naturality (hacyclic : PuncturedAcyclic N twoR z₀)
    {rel chart HrelE HE : ModuleCat.{0} (ZMod 2)} {r k : ℕ} (i₀ : Fin k)
    {relLoc : Fin k → ModuleCat.{0} (ZMod 2)}
    (j : rel ⟶ cohomologyZMod2 (TopCat.of N) twoR)
    (rho : ∀ i, relLoc i ⟶ rel)
    (jloc : ∀ i, relLoc i ⟶ cohomologyZMod2 (TopCat.of N) twoR)
    (hcompat : ∀ i, rho i ≫ j = jloc i)
    (ires : cohomologyZMod2 (TopCat.of N) twoR ⟶
      cohomologyZMod2 (TopCat.of ↥({z₀}ᶜ : Set N)) twoR)
    (hexact : LinearMap.range (jloc i₀).hom = LinearMap.ker ires.hom)
    (absLine : Nonempty (cohomologyZMod2 (TopCat.of N) twoR ≃ₗ[ZMod 2] ZMod 2))
    (exc : relLoc i₀ ≅ chart)
    (chartIso : chart ≅
      relCohomology (ZMod 2) (TopCat.of (Fin r → ℂ)) (puncturedSet r) (2 * r))
    (jE : HrelE ⟶ HE) (sRel : HrelE ⟶ rel)
    (sAbs : HE ⟶ cohomologyZMod2 (TopCat.of N) twoR)
    (piStar : cohomologyZMod2 (TopCat.of N) twoR ⟶ HE)
    (hnat : sRel ≫ j = jE ≫ sAbs)
    (hsection : piStar ≫ sAbs = 𝟙 (cohomologyZMod2 (TopCat.of N) twoR))
    {u : HrelE} {xloc : ∀ i, relLoc i} (hsplit : LocalSplit rho (sRel.hom u) xloc)
    (hx : xloc i₀ ≠ 0)
    {c : cohomologyZMod2 (TopCat.of N) twoR} (hloc : LocalClassesAgree jloc xloc c)
    (hk : ((k : ℕ) : ZMod 2) ≠ 0)
    {gamma : cohomologyZMod2 (TopCat.of N) twoR}
    (hu : jE.hom u = piStar.hom gamma) :
    gamma ≠ 0 := by
  have hgamma : j.hom (sRel.hom u) = gamma :=
    topClass_eq_of_naturality' jE j sRel sAbs piStar hnat hsection hu
  rw [← hgamma]
  exact topChernClass_ne_zero_kzero hacyclic i₀ j rho jloc hcompat ires hexact absLine exc
    chartIso hsplit hx hloc hk

/-! Audited on every build: `#audit_axioms` prints the closure **and fails the build** if
it leaves the classical allowlist. -/

#audit_axioms topChernClass_ne_zero_kzero
#audit_axioms topChernClass_ne_zero_kzero_naturality

end GroupApproximation.CharClass
