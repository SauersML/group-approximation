import GroupApproximation.CharClass.CohomologyProjectiveParity

/-!
# No odd cohomology on a dependent product of projective spaces

`noOddCohomology_prod_CP` peels one projective factor off a **binary** product.
`cc-lix-odd`'s base is the dependent product `∀ j : Fin ℓ, ℂP^{d j}`, so the two
have to be bridged, and `cc-wu`'s last open hypothesis is the dependent one.

The bridge is the obvious splitting of a dependent product over `Fin (ℓ + 1)` into
the product over `Fin ℓ` and the last factor.  Mathlib has this for measurable
equivalences but not for homeomorphisms, so it is built here.

## Main results

* `KnCP.baseYSnocHomeo` — peel the last factor off a `Fin`-indexed product.
* `KnCP.noOddCohomology_piCP` — the dependent product has no odd cohomology.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.STW59
open GroupApproximation.CharClass.CPn

namespace GroupApproximation.CharClass

noncomputable section

namespace KnCP

/-- **Peeling the last factor off a dependent product over `Fin (ℓ + 1)`.** -/
def baseYSnocHomeo (ℓ : ℕ) (dd : Fin (ℓ + 1) → ℕ) :
    (∀ j : Fin (ℓ + 1), CP (dd j))
      ≃ₜ ((∀ i : Fin ℓ, CP (dd i.castSucc)) × CP (dd (Fin.last ℓ))) where
  toFun f := (fun i => f i.castSucc, f (Fin.last ℓ))
  invFun p := Fin.lastCases p.2 p.1
  left_inv f := by
    funext j
    refine Fin.lastCases ?_ ?_ j
    · simp
    · intro i
      simp
  right_inv p := by
    refine Prod.ext ?_ ?_
    · funext i
      simp
    · simp
  continuous_toFun :=
    Continuous.prodMk (continuous_pi fun i => continuous_apply _) (continuous_apply _)
  continuous_invFun := by
    refine continuous_pi fun j => ?_
    refine Fin.lastCases ?_ ?_ j
    · simpa using continuous_snd
    · intro i
      simpa using (continuous_apply i).fst'

/-- The absence of odd cohomology transports along a homeomorphism. -/
theorem noOddCohomology_of_homeomorph {A B : Type} [TopologicalSpace A]
    [TopologicalSpace B] (e : A ≃ₜ B) (hB : KnHemi.NoOddCohomology B) :
    KnHemi.NoOddCohomology A :=
  fun j hj => isZero_of_linearEquiv (pullEquivOfHomeomorph e j) (hB j hj)

/-- **A dependent product of projective spaces has no odd cohomology.**  This is the
form `cc-wu`'s `ChernSplit` hypothesis needs, since `cc-lix-odd`'s base is
`∀ j : Fin ℓ, ℂP^{d j}` rather than an iterated binary product. -/
theorem noOddCohomology_piCP :
    ∀ (ℓ : ℕ) (dd : Fin ℓ → ℕ),
      KnHemi.NoOddCohomology (∀ j : Fin ℓ, CP (dd j)) := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro dd j hj
    haveI : Subsingleton (∀ j : Fin 0, CP (dd j)) :=
      ⟨fun f g => funext fun i => i.elim0⟩
    haveI : Nonempty (∀ j : Fin 0, CP (dd j)) := ⟨fun i => i.elim0⟩
    exact cohomology_isZero_of_contractible _ j (by rw [Nat.odd_iff] at hj; omega)
  | succ e ih =>
    intro dd
    refine noOddCohomology_of_homeomorph (baseYSnocHomeo e dd) ?_
    exact noOddCohomology_prod_CP _ (ih fun i => dd i.castSucc) (dd (Fin.last e))

end KnCP

end

end GroupApproximation.CharClass
