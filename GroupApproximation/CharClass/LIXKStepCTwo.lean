import GroupApproximation.CharClass.LIXKStepC
import GroupApproximation.Meta.AxiomGuard

/-!
# The `k`-zero Step C at mod-2 coefficients, with no transport at all

Lane `sp-oddside` of the STW Problem LIX strengthening
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.3.4).

`CharClass/LIXKStepC.lean` leaves `LocalClassesAgree` — that the `k` local classes have a
common image `c` — as an abstract hypothesis, because its two discharges have different
shapes.  This file gives the mod-2 one, and it is the observation `sp-design` sent in their
review of this lane (2026-09-10), which removes the entire rotation apparatus from the `F₂`
deliverable:

> `H^{2r}(N; F₂)` is a line, so an `F₂`-line has a **unique** nonzero element.  Hence
> `j_i(x_i) = j_{i₀}(x_{i₀})` for every `i` as soon as each `j_i(x_i)` is nonzero, and each
> of those is the one-zero argument run at `z_i`.

So at `p = 2` there is **no isotopy `ρ_t`, no naturality square along `ρ^i`, and no
homotopy invariance of any kind** — none of `sp-design` §4.1's Half A or Half B is needed.
In particular `CharClass/RelativeLineHomotopy.lean` is not imported here and must not be:
it is mod-2-only by its own docstring, so a dependency on it would have to be torn out
again for the odd-`p` deliverable.  The fact actually used is `eq_of_ne_zero_of_line_two`
below, which is `decide` on `ZMod 2` transported along the line.

## What this route costs instead

`PuncturedAcyclic N (2r) z_i` at **every** zero, not only at the distinguished one — because
the one-zero argument is now run `k` times.  That is free for the LIX base:
`LIXKStepCWired.puncturedAcyclic_lixPoint` already takes the point as an argument.  This is
the caveat `sp-design` attached to "the `k`-point punctured vanishing is off the critical
path": the `k`-point statement is, the one-point statement at each `z_i` is not.

At odd `p` the line has `p − 1` nonzero elements and this argument says nothing; there the
discharge is the rotation transport and needs `sp-coeff`'s relative homotopy invariance.

## Main declarations

* `eq_of_ne_zero_of_line_two` — an `F₂`-line has a unique nonzero element.
* `localClassesAgree_of_ne_zero_two` — **the discharge**, from nonvanishing alone.
* `localClass_ne_zero` — the one-zero argument at one `z_i`, in the shape needed.
* `topChernClass_ne_zero_kzero_two` — **the `k`-zero Step C over `F₂`**, with
  `LocalClassesAgree` gone and per-zero one-zero data in its place.
-/

noncomputable section

namespace GroupApproximation.CharClass

open CategoryTheory Limits
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-! ## 1. An `F₂`-line has a unique nonzero element -/

/-- **Two nonzero elements of an `F₂`-line are equal.**  Over any other field they differ by
a scalar and this is false, which is exactly why `LocalClassesAgree` is left abstract in
`CharClass/LIXKCount.lean`. -/
theorem eq_of_ne_zero_of_line_two {A : ModuleCat.{0} (ZMod 2)}
    (e : A ≃ₗ[ZMod 2] ZMod 2) {a b : A} (ha : a ≠ 0) (hb : b ≠ 0) : a = b := by
  have hone : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
  have ha' : e a = 1 := hone _ fun h => ha (e.map_eq_zero_iff.mp h)
  have hb' : e b = 1 := hone _ fun h => hb (e.map_eq_zero_iff.mp h)
  exact e.injective (by rw [ha', hb'])

/-- **`LocalClassesAgree`, discharged at mod-2 coefficients from nonvanishing alone.** -/
theorem localClassesAgree_of_ne_zero_two {A : ModuleCat.{0} (ZMod 2)} {k : ℕ}
    {relLoc : Fin k → ModuleCat.{0} (ZMod 2)}
    (jloc : ∀ i, relLoc i ⟶ A) (xloc : ∀ i, relLoc i)
    (e : A ≃ₗ[ZMod 2] ZMod 2) (hne : ∀ i, (jloc i).hom (xloc i) ≠ 0) (i₀ : Fin k) :
    LocalClassesAgree jloc xloc ((jloc i₀).hom (xloc i₀)) :=
  fun i => eq_of_ne_zero_of_line_two e (hne i) (hne i₀)

/-! ## 2. The one-zero argument, at one zero -/

variable {N : Type} [TopologicalSpace N] {twoR : ℕ}

/-- **The one-zero Step C, in the shape the `k`-zero count consumes**: at a zero where the
relative class is nonzero, its image in the absolute group is nonzero.

This is `ThomStepCEuler.topChernClass_ne_zero_of_su_ne_zero_line` with `gamma` taken to be
the image itself, so `hgamma` is `rfl`. -/
theorem localClass_ne_zero {z : N} (hacyclic : PuncturedAcyclic N twoR z)
    {rel chart : ModuleCat.{0} (ZMod 2)} {r : ℕ}
    (j : rel ⟶ cohomologyZMod2 (TopCat.of N) twoR)
    (ires : cohomologyZMod2 (TopCat.of N) twoR ⟶
      cohomologyZMod2 (TopCat.of ↥({z}ᶜ : Set N)) twoR)
    (hexact : LinearMap.range j.hom = LinearMap.ker ires.hom)
    (absLine : Nonempty (cohomologyZMod2 (TopCat.of N) twoR ≃ₗ[ZMod 2] ZMod 2))
    (exc : rel ≅ chart)
    (chartIso : chart ≅
      relCohomology (ZMod 2) (TopCat.of (Fin r → ℂ)) (puncturedSet r) (2 * r))
    {su : rel} (hne : su ≠ 0) :
    j.hom su ≠ 0 :=
  topChernClass_ne_zero_of_su_ne_zero_line hacyclic j ires hexact absLine exc chartIso hne
    rfl

/-! ## 3. The `k`-zero Step C over `F₂` -/

/-- **Step C's odd side with `k` zeros, at mod-2 coefficients.**

`LocalClassesAgree` is gone.  In its place every zero carries the one-zero Step C's own
data — punctured acyclicity at `z i`, the exact sequence there, and the excision/chart
identification of that pair with the local model — and the `k` local classes are then equal
because an `F₂`-line has one nonzero element.

Compared with `topChernClass_ne_zero_kzero`, this trades one abstract hypothesis for `k`
copies of data the tree already produces at every point of the LIX base. -/
theorem topChernClass_ne_zero_kzero_two {k r : ℕ} (i₀ : Fin k)
    {rel : ModuleCat.{0} (ZMod 2)} {relLoc chart : Fin k → ModuleCat.{0} (ZMod 2)}
    (z : Fin k → N) (hac : ∀ i, PuncturedAcyclic N twoR (z i))
    (j : rel ⟶ cohomologyZMod2 (TopCat.of N) twoR)
    (rho : ∀ i, relLoc i ⟶ rel)
    (jloc : ∀ i, relLoc i ⟶ cohomologyZMod2 (TopCat.of N) twoR)
    (hcompat : ∀ i, rho i ≫ j = jloc i)
    (ires : ∀ i, cohomologyZMod2 (TopCat.of N) twoR ⟶
      cohomologyZMod2 (TopCat.of ↥({z i}ᶜ : Set N)) twoR)
    (hexact : ∀ i, LinearMap.range (jloc i).hom = LinearMap.ker (ires i).hom)
    (absLine : Nonempty (cohomologyZMod2 (TopCat.of N) twoR ≃ₗ[ZMod 2] ZMod 2))
    (exc : ∀ i, relLoc i ≅ chart i)
    (chartIso : ∀ i, chart i ≅
      relCohomology (ZMod 2) (TopCat.of (Fin r → ℂ)) (puncturedSet r) (2 * r))
    {x : rel} {xloc : ∀ i, relLoc i} (hsplit : LocalSplit rho x xloc)
    (hx : ∀ i, xloc i ≠ 0) (hk : ((k : ℕ) : ZMod 2) ≠ 0) :
    j.hom x ≠ 0 := by
  obtain ⟨e⟩ := absLine
  have hne : ∀ i, (jloc i).hom (xloc i) ≠ 0 := fun i =>
    localClass_ne_zero (hac i) (jloc i) (ires i) (hexact i) ⟨e⟩ (exc i) (chartIso i) (hx i)
  exact map_ne_zero_of_localSplit j rho jloc hcompat hsplit
    (localClassesAgree_of_ne_zero_two jloc xloc e hne i₀) (hne i₀) hk

/-! Audited on every build. -/

#audit_axioms eq_of_ne_zero_of_line_two
#audit_axioms localClassesAgree_of_ne_zero_two
#audit_axioms topChernClass_ne_zero_kzero_two

end GroupApproximation.CharClass
