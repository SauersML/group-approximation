import GroupApproximation.Matching.FiniteGroupoidPresentation
import GroupApproximation.Matching.FinitePartialBijection

/-!
# Finite cluster groupoids of partial bijections

This is the finite-stage counterpart of the asymptotic partial-bijection
groupoid.  Candidate partial bijections have small missing mass.  Composition
is followed by a specified improvement map.  A gap at eight times the small
radius turns the resulting near relation into an equivalence relation and
proves every groupoid law.
-/

namespace GroupApproximation

universe u

/-- Finite data sufficient to build a groupoid of clusters of co-large
partial bijections.  All quantitative hypotheses concern explicit finite
cardinalities. -/
structure FinitePartialClusterData (I : Type u) [Fintype I] where
  model : I → FiniteModel
  radius : ℕ
  radius_pos : 0 < radius
  candidate : ∀ X Y, Finset (FinitePartialBijection (model X) (model Y))
  one_mem : ∀ X, FinitePartialBijection.refl (model X) ∈ candidate X X
  symm_mem : ∀ {X Y} (f : FinitePartialBijection (model X) (model Y)),
    f ∈ candidate X Y → f.symm ∈ candidate Y X
  improve : ∀ {X Y Z},
    FinitePartialBijection (model X) (model Y) →
    FinitePartialBijection (model Y) (model Z) →
    FinitePartialBijection (model X) (model Z)
  improve_mem : ∀ {X Y Z}
    (f : FinitePartialBijection (model X) (model Y)),
    f ∈ candidate X Y →
    ∀ (g : FinitePartialBijection (model Y) (model Z)),
    g ∈ candidate Y Z → improve f g ∈ candidate X Z
  improve_close : ∀ {X Y Z}
    (f : FinitePartialBijection (model X) (model Y)),
    f ∈ candidate X Y →
    ∀ (g : FinitePartialBijection (model Y) (model Z)),
    g ∈ candidate Y Z →
      (improve f g).twoSidedDisagreement (f.trans g) < radius
  self_small : ∀ {X Y}
    (f : FinitePartialBijection (model X) (model Y)),
    f ∈ candidate X Y → f.sourceDefect + f.targetDefect < radius
  gap : ∀ {X Y}
    (f : FinitePartialBijection (model X) (model Y)),
    f ∈ candidate X Y →
    ∀ (g : FinitePartialBijection (model X) (model Y)),
    g ∈ candidate X Y →
      f.twoSidedDisagreement g < radius ∨
        8 * radius ≤ f.twoSidedDisagreement g

namespace FinitePartialClusterData

variable {I : Type u} [Fintype I] (D : FinitePartialClusterData I)

/-- Candidate representatives between two objects. -/
abbrev Rep (X Y : I) :=
  {f : FinitePartialBijection (D.model X) (D.model Y) //
    f ∈ D.candidate X Y}

noncomputable instance repFintype (X Y : I) : Fintype (D.Rep X Y) :=
  Fintype.ofFinset (D.candidate X Y) fun _ ↦ Iff.rfl

/-- Two candidates are in the same small cluster. -/
def Near {X Y : I} (f g : D.Rep X Y) : Prop :=
  f.1.twoSidedDisagreement g.1 < D.radius

theorem near_of_lt_eight {X Y : I} {f g : D.Rep X Y}
    (h : f.1.twoSidedDisagreement g.1 < 8 * D.radius) : D.Near f g := by
  rcases D.gap f.1 f.2 g.1 g.2 with hnear | hfar
  · exact hnear
  · omega

theorem near_refl {X Y : I} (f : D.Rep X Y) : D.Near f f := by
  rw [Near, FinitePartialBijection.twoSidedDisagreement_self]
  exact D.self_small f.1 f.2

theorem near_symm {X Y : I} {f g : D.Rep X Y}
    (h : D.Near f g) : D.Near g f := by
  rw [Near, FinitePartialBijection.twoSidedDisagreement_comm]
  exact h

theorem near_trans {X Y : I} {f g h : D.Rep X Y}
    (hfg : D.Near f g) (hgh : D.Near g h) : D.Near f h := by
  apply D.near_of_lt_eight
  have htri := FinitePartialBijection.twoSidedDisagreement_le f.1 g.1 h.1
  unfold Near at hfg hgh
  omega

/-- The small-cluster relation on finite representatives. -/
def nearSetoid (X Y : I) : Setoid (D.Rep X Y) where
  r := Near D
  iseqv := ⟨D.near_refl, fun {_ _} ↦ D.near_symm,
    fun {_ _ _} ↦ D.near_trans⟩

private def roundedComp {X Y Z : I} (f : D.Rep X Y) (g : D.Rep Y Z) :
    D.Rep X Z :=
  ⟨D.improve f.1 g.1, D.improve_mem f.1 f.2 g.1 g.2⟩

private def reversed {X Y : I} (f : D.Rep X Y) : D.Rep Y X :=
  ⟨f.1.symm, D.symm_mem f.1 f.2⟩

private theorem roundedComp_congr {X Y Z : I}
    {f f' : D.Rep X Y} {g g' : D.Rep Y Z}
    (hf : D.Near f f') (hg : D.Near g g') :
    D.Near (roundedComp D f g) (roundedComp D f' g') := by
  apply D.near_of_lt_eight
  change (D.improve f.1 g.1).twoSidedDisagreement
    (D.improve f'.1 g'.1) < 8 * D.radius
  have hleft := D.improve_close f.1 f.2 g.1 g.2
  have hright := D.improve_close f'.1 f'.2 g'.1 g'.2
  have hmiddle := FinitePartialBijection.twoSidedDisagreement_trans_le
    f.1 f'.1 g.1 g'.1
  have htri₁ := FinitePartialBijection.twoSidedDisagreement_le
    (D.improve f.1 g.1) (f.1.trans g.1) (f'.1.trans g'.1)
  have htri₂ := FinitePartialBijection.twoSidedDisagreement_le
    (D.improve f.1 g.1) (f'.1.trans g'.1) (D.improve f'.1 g'.1)
  have hright' : (f'.1.trans g'.1).twoSidedDisagreement
      (D.improve f'.1 g'.1) < D.radius := by
    rw [FinitePartialBijection.twoSidedDisagreement_comm]
    exact hright
  unfold Near at hf hg
  omega

private theorem reversed_congr {X Y : I} {f g : D.Rep X Y}
    (h : D.Near f g) : D.Near (reversed D f) (reversed D g) := by
  unfold Near at h ⊢
  change f.1.symm.twoSidedDisagreement g.1.symm < D.radius
  rw [FinitePartialBijection.twoSidedDisagreement_symm]
  exact h

private theorem roundedComp_one_left {X Y : I} (f : D.Rep X Y) :
    D.Near (roundedComp D ⟨FinitePartialBijection.refl _, D.one_mem X⟩ f) f := by
  have hclose := D.improve_close
    (FinitePartialBijection.refl (D.model X)) (D.one_mem X) f.1 f.2
  change (D.improve (FinitePartialBijection.refl (D.model X)) f.1).twoSidedDisagreement
    f.1 < D.radius
  simpa only [FinitePartialBijection.refl_trans] using hclose

private theorem roundedComp_one_right {X Y : I} (f : D.Rep X Y) :
    D.Near (roundedComp D f ⟨FinitePartialBijection.refl _, D.one_mem Y⟩) f := by
  have hclose := D.improve_close f.1 f.2
    (FinitePartialBijection.refl (D.model Y)) (D.one_mem Y)
  change (D.improve f.1 (FinitePartialBijection.refl (D.model Y))).twoSidedDisagreement
    f.1 < D.radius
  simpa only [FinitePartialBijection.trans_refl] using hclose

private theorem roundedComp_assoc {W X Y Z : I}
    (f : D.Rep W X) (g : D.Rep X Y) (h : D.Rep Y Z) :
    D.Near (roundedComp D (roundedComp D f g) h)
      (roundedComp D f (roundedComp D g h)) := by
  apply D.near_of_lt_eight
  change (D.improve (D.improve f.1 g.1) h.1).twoSidedDisagreement
    (D.improve f.1 (D.improve g.1 h.1)) < 8 * D.radius
  have hfgMem := D.improve_mem f.1 f.2 g.1 g.2
  have hghMem := D.improve_mem g.1 g.2 h.1 h.2
  have houterL := D.improve_close
    (D.improve f.1 g.1) hfgMem h.1 h.2
  have houterR := D.improve_close f.1 f.2
    (D.improve g.1 h.1) hghMem
  have hfg := D.improve_close f.1 f.2 g.1 g.2
  have hgh := D.improve_close g.1 g.2 h.1 h.2
  have hselfF := D.self_small f.1 f.2
  have hselfH := D.self_small h.1 h.2
  have hleftLe := FinitePartialBijection.twoSidedDisagreement_trans_le
    (D.improve f.1 g.1) (f.1.trans g.1) h.1 h.1
  have hrightLe := FinitePartialBijection.twoSidedDisagreement_trans_le
    f.1 f.1 (g.1.trans h.1) (D.improve g.1 h.1)
  rw [FinitePartialBijection.twoSidedDisagreement_self] at hleftLe hrightLe
  have hleftLt : ((D.improve f.1 g.1).trans h.1).twoSidedDisagreement
      ((f.1.trans g.1).trans h.1) < 2 * D.radius := by omega
  have hgh' : (g.1.trans h.1).twoSidedDisagreement
      (D.improve g.1 h.1) < D.radius := by
    rw [FinitePartialBijection.twoSidedDisagreement_comm]
    exact hgh
  have hrightLt : (f.1.trans (g.1.trans h.1)).twoSidedDisagreement
      (f.1.trans (D.improve g.1 h.1)) < 2 * D.radius := by omega
  have hassoc : (f.1.trans g.1).trans h.1 = f.1.trans (g.1.trans h.1) :=
    f.1.trans_assoc g.1 h.1
  have htri₁ := FinitePartialBijection.twoSidedDisagreement_le
    (D.improve (D.improve f.1 g.1) h.1)
      ((D.improve f.1 g.1).trans h.1) ((f.1.trans g.1).trans h.1)
  have htri₂ := FinitePartialBijection.twoSidedDisagreement_le
    (D.improve (D.improve f.1 g.1) h.1) ((f.1.trans g.1).trans h.1)
      (f.1.trans (D.improve g.1 h.1))
  have htri₃ := FinitePartialBijection.twoSidedDisagreement_le
    (D.improve (D.improve f.1 g.1) h.1)
      (f.1.trans (D.improve g.1 h.1))
      (D.improve f.1 (D.improve g.1 h.1))
  have houterR' : (f.1.trans (D.improve g.1 h.1)).twoSidedDisagreement
      (D.improve f.1 (D.improve g.1 h.1)) < D.radius := by
    rw [FinitePartialBijection.twoSidedDisagreement_comm]
    exact houterR
  rw [hassoc] at hleftLt htri₁ htri₂
  omega

private theorem roundedComp_inv_left {X Y : I} (f : D.Rep X Y) :
    D.Near (roundedComp D (reversed D f) f)
      ⟨FinitePartialBijection.refl _, D.one_mem Y⟩ := by
  apply D.near_of_lt_eight
  change (D.improve f.1.symm f.1).twoSidedDisagreement
    (FinitePartialBijection.refl (D.model Y)) < 8 * D.radius
  have hclose := D.improve_close f.1.symm (D.symm_mem f.1 f.2) f.1 f.2
  have hid := FinitePartialBijection.twoSidedDisagreement_reflOn_refl f.1.target
  have hid' : (FinitePartialBijection.reflOn f.1.target).twoSidedDisagreement
      (FinitePartialBijection.refl (D.model Y)) = 2 * f.1.targetDefect := by
    simpa [FinitePartialBijection.targetDefect] using hid
  have hself := D.self_small f.1 f.2
  have htarget : f.1.targetDefect < D.radius := by omega
  have htri := FinitePartialBijection.twoSidedDisagreement_le
    (D.improve f.1.symm f.1) (f.1.symm.trans f.1)
      (FinitePartialBijection.refl (D.model Y))
  rw [f.1.symm_trans_self] at hclose htri
  rw [hid'] at htri
  omega

private theorem roundedComp_inv_right {X Y : I} (f : D.Rep X Y) :
    D.Near (roundedComp D f (reversed D f))
      ⟨FinitePartialBijection.refl _, D.one_mem X⟩ := by
  apply D.near_of_lt_eight
  change (D.improve f.1 f.1.symm).twoSidedDisagreement
    (FinitePartialBijection.refl (D.model X)) < 8 * D.radius
  have hclose := D.improve_close f.1 f.2 f.1.symm (D.symm_mem f.1 f.2)
  have hid := FinitePartialBijection.twoSidedDisagreement_reflOn_refl f.1.source
  have hid' : (FinitePartialBijection.reflOn f.1.source).twoSidedDisagreement
      (FinitePartialBijection.refl (D.model X)) = 2 * f.1.sourceDefect := by
    simpa [FinitePartialBijection.sourceDefect] using hid
  have hself := D.self_small f.1 f.2
  have hsource : f.1.sourceDefect < D.radius := by omega
  have htri := FinitePartialBijection.twoSidedDisagreement_le
    (D.improve f.1 f.1.symm) (f.1.trans f.1.symm)
      (FinitePartialBijection.refl (D.model X))
  rw [f.1.trans_symm] at hclose htri
  rw [hid'] at htri
  omega

/-- The finite groupoid presentation obtained from partial-bijection
clusters. -/
noncomputable def presentation : GroupoidPresentation I where
  Rep := D.Rep
  rel := D.nearSetoid
  one X := ⟨FinitePartialBijection.refl _, D.one_mem X⟩
  comp := roundedComp D
  inv := reversed D
  comp_respects := roundedComp_congr D
  inv_respects := reversed_congr D
  one_comp := roundedComp_one_left D
  comp_one := roundedComp_one_right D
  assoc := roundedComp_assoc D
  inv_comp := roundedComp_inv_left D
  comp_inv := roundedComp_inv_right D

end FinitePartialClusterData
end GroupApproximation
