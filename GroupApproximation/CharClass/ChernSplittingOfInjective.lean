import GroupApproximation.CharClass.CupOneTotal
import GroupApproximation.CharClass.BundleFlagStage
import GroupApproximation.CharClass.CohomologyBridge

/-!
# The splitting principle over `K`, layer 2, item 1: injectivity of the flag pullback

Lane `lix-evenside`, prefix `CharClass/ChernSplittingOf*`.

`SplittingDataOf.pull_injective` asks for `Function.Injective (TotalHOf.map K proj)` at the
projection of the flag space.  This file is the coefficient-generic port of
`ParityEvenTransport`/`ParityEvenFlag`: functoriality of `TotalHOf.map`, ring-level injectivity
from degreewise injectivity of `pull`, and the induction up the flag tower
`Flag p (n+1) ≃ₜ Proj (flagRest p n)`.  The per-stage input — degreewise injectivity of the
pullback along each projective bundle `Proj (flagRest p n) → Flag p n`, `n < r` — is Leray–Hirsch
over a compact base, and stays a hypothesis here.

Nothing uses the coefficient ring beyond `[CommRing K]`, and nothing uses commutativity of the
cohomology ring.

## Main results

* `ChernSplittingOf.totalHOf_map_id`, `totalHOf_map_comp` — functoriality.
* `ChernSplittingOf.totalHOf_component_map` — a component of a pullback is the pullback of the
  component.
* `ChernSplittingOf.totalHOf_map_injective` — degreewise injectivity gives ring-level injectivity.
* `ChernSplittingOf.flagProj_map_injective_of_proj` — the whole tower, from the per-stage input.
-/

set_option autoImplicit false

open CategoryTheory

namespace GroupApproximation.CharClass

namespace ChernSplittingOf

noncomputable section

/-! ## 1. Functoriality and components -/

section Functoriality

variable {K : Type} [CommRing K]

theorem totalHOf_map_id (X : TopCat.{0}) (c : TotalHOf K X) : TotalHOf.map K (𝟙 X) c = c := by
  induction c using DirectSum.induction_on with
  | zero => rw [map_zero]
  | of n a =>
    show TotalHOf.map K (𝟙 X) (TotalHOf.of K X n a) = TotalHOf.of K X n a
    rw [TotalHOf.map_of, pull_id]
  | add c₁ c₂ h₁ h₂ => rw [map_add, h₁, h₂]

theorem totalHOf_map_comp {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (c : TotalHOf K Z) :
    TotalHOf.map K (f ≫ g) c = TotalHOf.map K f (TotalHOf.map K g c) := by
  induction c using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | of n a =>
    show TotalHOf.map K (f ≫ g) (TotalHOf.of K Z n a)
      = TotalHOf.map K f (TotalHOf.map K g (TotalHOf.of K Z n a))
    rw [TotalHOf.map_of, TotalHOf.map_of, TotalHOf.map_of, pull_comp]
  | add c₁ c₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add]

theorem totalHOf_component_map {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) (c : TotalHOf K Y) :
    TotalHOf.component K X n (TotalHOf.map K f c) = pull f n (TotalHOf.component K Y n c) := by
  induction c using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, pull_zero]
  | of m a =>
    show TotalHOf.component K X n (TotalHOf.map K f (TotalHOf.of K Y m a))
      = pull f n (TotalHOf.component K Y n (TotalHOf.of K Y m a))
    rw [TotalHOf.map_of]
    rcases eq_or_ne n m with rfl | hnm
    · rw [TotalHOf.component_of, TotalHOf.component_of]
    · rw [TotalHOf.component_of_ne K X hnm, TotalHOf.component_of_ne K Y hnm, pull_zero]
  | add u v hu hv => rw [map_add, map_add, map_add, hu, hv, pull_add]

/-- **Degreewise injectivity gives ring-level injectivity.** -/
theorem totalHOf_map_injective {X Y : TopCat.{0}} (f : X ⟶ Y)
    (h : ∀ n : ℕ, Function.Injective (pull (K := K) f n)) :
    Function.Injective (TotalHOf.map K f) := by
  intro c c' hcc
  ext n
  refine h n ?_
  show pull f n (TotalHOf.component K Y n c) = pull f n (TotalHOf.component K Y n c')
  rw [← totalHOf_component_map, ← totalHOf_component_map, hcc]

/-- Injectivity composes along `≫`. -/
theorem totalHOf_map_injective_comp {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Function.Injective (TotalHOf.map K f)) (hg : Function.Injective (TotalHOf.map K g)) :
    Function.Injective (TotalHOf.map K (f ≫ g)) := by
  intro c c' hcc
  rw [totalHOf_map_comp, totalHOf_map_comp] at hcc
  exact hg (hf hcc)

/-- **Injectivity from a continuous left inverse.**  Stated with `cmap`, as in the `F₂` file. -/
theorem totalHOf_map_injective_of_leftInv {A B : Type} [TopologicalSpace A]
    [TopologicalSpace B] (f : C(A, B)) (g : C(B, A)) (hfg : ∀ b, f (g b) = b) :
    Function.Injective (TotalHOf.map K (cmap f)) := by
  have hcomp : cmap g ≫ cmap f = 𝟙 (TopCat.of B) := by
    apply TopCat.ext
    intro b
    exact hfg b
  intro c c' hcc
  have h2 := congrArg (TotalHOf.map K (cmap g)) hcc
  rw [← totalHOf_map_comp, ← totalHOf_map_comp, hcomp, totalHOf_map_id, totalHOf_map_id] at h2
  exact h2

end Functoriality

/-! ## 2. The flag tower -/

section Flag

variable {K : Type} [CommRing K] {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι]

/-- One stage of the tower: the forgetful map is the projection of the rest bundle after the
identification `flagSucc`. -/
theorem flagForget_map_injective (p : Bundle X ι) (n : ℕ)
    (h : Function.Injective
      (TotalHOf.map K (cmap (Bundle.projPi (Bundle.flagRest p n))))) :
    Function.Injective (TotalHOf.map K (cmap (Bundle.flagForget p n))) := by
  have hfe : cmap (Bundle.flagForget p n)
      = cmap (Bundle.flagSucc p n) ≫ cmap (Bundle.projPi (Bundle.flagRest p n)) := by
    apply TopCat.ext
    intro w
    exact (Bundle.flagSucc_over_base p n w).symm
  rw [hfe]
  refine totalHOf_map_injective_comp _ _ ?_ h
  exact totalHOf_map_injective_of_leftInv _ (Bundle.flagSucc p n).symm
    (fun b => (Bundle.flagSucc p n).apply_symm_apply b)

/-- The base of the tower. -/
theorem flagProj_zero_map_injective (p : Bundle X ι) :
    Function.Injective (TotalHOf.map K (cmap (Bundle.flagProj p 0))) :=
  totalHOf_map_injective_of_leftInv _ (Bundle.flagZero p).symm
    (fun x => by
      rw [← Bundle.flagZero_eq_flagProj]
      exact (Bundle.flagZero p).apply_symm_apply x)

/-- **The whole tower**, from injectivity at each forgetful stage below the height. -/
theorem flagProj_map_injective (p : Bundle X ι) :
    ∀ r : ℕ, (∀ n : ℕ, n < r →
        Function.Injective (TotalHOf.map K (cmap (Bundle.flagForget p n)))) →
      Function.Injective (TotalHOf.map K (cmap (Bundle.flagProj p r))) := by
  intro r
  induction r with
  | zero => intro _; exact flagProj_zero_map_injective p
  | succ r ih =>
    intro hstage
    have hcomp : cmap (Bundle.flagProj p (r + 1))
        = cmap (Bundle.flagForget p r) ≫ cmap (Bundle.flagProj p r) := by
      apply TopCat.ext
      intro w
      rfl
    rw [hcomp]
    exact totalHOf_map_injective_comp _ _ (hstage r (by omega))
      (ih fun n hn => hstage n (by omega))

/-- **The flag pullback is injective over `K`**, from degreewise injectivity of the pullback along
each projective bundle of the tower below the height (Leray–Hirsch over the stage). -/
theorem flagProj_map_injective_of_proj (p : Bundle X ι) (r : ℕ)
    (hproj : ∀ n : ℕ, n < r → ∀ k : ℕ,
      Function.Injective (pull (K := K) (cmap (Bundle.projPi (Bundle.flagRest p n))) k)) :
    Function.Injective (TotalHOf.map K (cmap (Bundle.flagProj p r))) :=
  flagProj_map_injective p r fun n hn =>
    flagForget_map_injective p n (totalHOf_map_injective _ (hproj n hn))

end Flag

end

end ChernSplittingOf

end GroupApproximation.CharClass
