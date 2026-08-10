import NonsoficGroupsExist.Matching.FiniteGroupoidPresentation
import NonsoficGroupsExist.Matching.FinitePartialBijection

/-!
# Finite normalized cluster groupoids

The joint-scale cluster construction compares errors to the sizes of the two
endpoint components, not to one absolute cardinal radius shared by every
component.  This file provides the corresponding finite groupoid theorem.

For objects `X,Y`, put `mass X Y = |X| + |Y|`.  Two representatives are in
the same cluster when five times their two-sided disagreement is smaller than
that mass.  Candidate separation supplies the complementary gap at four
fifths of the mass.  Improvements and candidate self-defects are required to
be below one hundredth of the relevant mass.  The only size bookkeeping is
the explicit factor-three comparison for consecutive candidates and for the
two endpoints of one candidate.

All hypotheses are finite cardinal inequalities.  The theorem below proves
the equivalence relation and every groupoid law; no asymptotic statement or
stability input occurs here.
-/

namespace NonsoficGroupsExist

universe u

/-- Finite normalized data sufficient to construct a cluster groupoid from
co-large partial bijections between components of varying sizes. -/
structure FiniteNormalizedPartialClusterData (I : Type u) [Fintype I] where
  model : I → FiniteModel
  card_pos : ∀ X, 0 < Fintype.card (model X)
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
  /-- Improvements change fewer than one hundredth of the endpoint mass. -/
  improve_close : ∀ {X Y Z}
    (f : FinitePartialBijection (model X) (model Y)),
    f ∈ candidate X Y →
    ∀ (g : FinitePartialBijection (model Y) (model Z)),
    g ∈ candidate Y Z →
      100 * (improve f g).twoSidedDisagreement (f.trans g) <
        Fintype.card (model X) + Fintype.card (model Z)
  /-- A candidate's missing mass is below one hundredth of its endpoint
  mass. -/
  self_small : ∀ {X Y}
    (f : FinitePartialBijection (model X) (model Y)),
    f ∈ candidate X Y →
      100 * (f.sourceDefect + f.targetDefect) <
        Fintype.card (model X) + Fintype.card (model Y)
  /-- Consecutive candidates have middle mass controlled by endpoint mass. -/
  middle_mass : ∀ {X Y Z}
    (f : FinitePartialBijection (model X) (model Y)),
    f ∈ candidate X Y →
    ∀ (g : FinitePartialBijection (model Y) (model Z)),
    g ∈ candidate Y Z →
      (Fintype.card (model X) + Fintype.card (model Y)) +
        (Fintype.card (model Y) + Fintype.card (model Z)) ≤
          3 * (Fintype.card (model X) + Fintype.card (model Z))
  /-- Each endpoint mass controls the joint mass of a candidate. -/
  endpoint_mass : ∀ {X Y}
    (f : FinitePartialBijection (model X) (model Y)),
    f ∈ candidate X Y →
      Fintype.card (model X) + Fintype.card (model Y) ≤
          3 * (Fintype.card (model X) + Fintype.card (model X)) ∧
        Fintype.card (model X) + Fintype.card (model Y) ≤
          3 * (Fintype.card (model Y) + Fintype.card (model Y))
  /-- Candidate separation at normalized thresholds one fifth and four
  fifths. -/
  gap : ∀ {X Y}
    (f : FinitePartialBijection (model X) (model Y)),
    f ∈ candidate X Y →
    ∀ (g : FinitePartialBijection (model X) (model Y)),
    g ∈ candidate X Y →
      5 * f.twoSidedDisagreement g <
          Fintype.card (model X) + Fintype.card (model Y) ∨
        4 * (Fintype.card (model X) + Fintype.card (model Y)) ≤
          5 * f.twoSidedDisagreement g

namespace FiniteNormalizedPartialClusterData

variable {I : Type u} [Fintype I]
variable (D : FiniteNormalizedPartialClusterData I)

/-- Sum of the cardinalities of two endpoint components. -/
def mass (X Y : I) : ℕ :=
  Fintype.card (D.model X) + Fintype.card (D.model Y)

theorem mass_pos (X Y : I) : 0 < D.mass X Y := by
  unfold mass
  omega

/-- Candidate representatives between two objects. -/
abbrev Rep (X Y : I) :=
  {f : FinitePartialBijection (D.model X) (D.model Y) //
    f ∈ D.candidate X Y}

noncomputable instance repFintype (X Y : I) : Fintype (D.Rep X Y) :=
  Fintype.ofFinset (D.candidate X Y) fun _ ↦ Iff.rfl

/-- The normalized one-fifth cluster relation. -/
def Near {X Y : I} (f g : D.Rep X Y) : Prop :=
  5 * f.1.twoSidedDisagreement g.1 < D.mass X Y

/-- Any pair strictly below the far threshold belongs to the small cluster. -/
theorem near_of_lt_far {X Y : I} {f g : D.Rep X Y}
    (h : 5 * f.1.twoSidedDisagreement g.1 < 4 * D.mass X Y) :
    D.Near f g := by
  rcases D.gap f.1 f.2 g.1 g.2 with hnear | hfar
  · exact hnear
  · unfold mass at h hfar
    omega

theorem near_refl {X Y : I} (f : D.Rep X Y) : D.Near f f := by
  unfold Near mass
  rw [FinitePartialBijection.twoSidedDisagreement_self]
  have h := D.self_small f.1 f.2
  omega

theorem near_symm {X Y : I} {f g : D.Rep X Y}
    (h : D.Near f g) : D.Near g f := by
  unfold Near at h ⊢
  rw [FinitePartialBijection.twoSidedDisagreement_comm]
  exact h

theorem near_trans {X Y : I} {f g h : D.Rep X Y}
    (hfg : D.Near f g) (hgh : D.Near g h) : D.Near f h := by
  apply D.near_of_lt_far
  have htri := FinitePartialBijection.twoSidedDisagreement_le f.1 g.1 h.1
  unfold Near at hfg hgh
  have hm := D.mass_pos X Y
  omega

/-- The normalized cluster relation as a setoid. -/
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
  apply D.near_of_lt_far
  have hleft := D.improve_close f.1 f.2 g.1 g.2
  have hright := D.improve_close f'.1 f'.2 g'.1 g'.2
  have hmiddle := FinitePartialBijection.twoSidedDisagreement_trans_le
    f.1 f'.1 g.1 g'.1
  have htri₁ := FinitePartialBijection.twoSidedDisagreement_le
    (D.improve f.1 g.1) (f.1.trans g.1) (f'.1.trans g'.1)
  have htri₂ := FinitePartialBijection.twoSidedDisagreement_le
    (D.improve f.1 g.1) (f'.1.trans g'.1) (D.improve f'.1 g'.1)
  have hright' : (f'.1.trans g'.1).twoSidedDisagreement
      (D.improve f'.1 g'.1) =
      (D.improve f'.1 g'.1).twoSidedDisagreement (f'.1.trans g'.1) := by
    rw [FinitePartialBijection.twoSidedDisagreement_comm]
  have hmass := D.middle_mass f.1 f.2 g.1 g.2
  unfold Near mass at hf hg ⊢
  rw [hright'] at htri₂
  omega

private theorem reversed_congr {X Y : I} {f g : D.Rep X Y}
    (h : D.Near f g) : D.Near (reversed D f) (reversed D g) := by
  unfold Near mass at h ⊢
  change 5 * f.1.symm.twoSidedDisagreement g.1.symm < _
  rw [FinitePartialBijection.twoSidedDisagreement_symm]
  simpa [Nat.add_comm] using h

private theorem roundedComp_one_left {X Y : I} (f : D.Rep X Y) :
    D.Near (roundedComp D ⟨FinitePartialBijection.refl _, D.one_mem X⟩ f) f := by
  unfold Near mass
  have hclose := D.improve_close
    (FinitePartialBijection.refl (D.model X)) (D.one_mem X) f.1 f.2
  simpa only [FinitePartialBijection.refl_trans] using
    (show 5 * (D.improve (FinitePartialBijection.refl (D.model X)) f.1).
      twoSidedDisagreement f.1 <
        Fintype.card (D.model X) + Fintype.card (D.model Y) by omega)

private theorem roundedComp_one_right {X Y : I} (f : D.Rep X Y) :
    D.Near (roundedComp D f ⟨FinitePartialBijection.refl _, D.one_mem Y⟩) f := by
  unfold Near mass
  have hclose := D.improve_close f.1 f.2
    (FinitePartialBijection.refl (D.model Y)) (D.one_mem Y)
  simpa only [FinitePartialBijection.trans_refl] using
    (show 5 * (D.improve f.1 (FinitePartialBijection.refl (D.model Y))).
      twoSidedDisagreement f.1 <
        Fintype.card (D.model X) + Fintype.card (D.model Y) by omega)

private theorem roundedComp_assoc {W X Y Z : I}
    (f : D.Rep W X) (g : D.Rep X Y) (h : D.Rep Y Z) :
    D.Near (roundedComp D (roundedComp D f g) h)
      (roundedComp D f (roundedComp D g h)) := by
  apply D.near_of_lt_far
  have hfgMem := D.improve_mem f.1 f.2 g.1 g.2
  have hghMem := D.improve_mem g.1 g.2 h.1 h.2
  have houterL := D.improve_close (D.improve f.1 g.1) hfgMem h.1 h.2
  have houterR := D.improve_close f.1 f.2 (D.improve g.1 h.1) hghMem
  have hfg := D.improve_close f.1 f.2 g.1 g.2
  have hgh := D.improve_close g.1 g.2 h.1 h.2
  have hselfF := D.self_small f.1 f.2
  have hselfH := D.self_small h.1 h.2
  have hleftLe := FinitePartialBijection.twoSidedDisagreement_trans_le
    (D.improve f.1 g.1) (f.1.trans g.1) h.1 h.1
  have hrightLe := FinitePartialBijection.twoSidedDisagreement_trans_le
    f.1 f.1 (g.1.trans h.1) (D.improve g.1 h.1)
  rw [FinitePartialBijection.twoSidedDisagreement_self] at hleftLe hrightLe
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
      (D.improve f.1 (D.improve g.1 h.1)) =
      (D.improve f.1 (D.improve g.1 h.1)).twoSidedDisagreement
        (f.1.trans (D.improve g.1 h.1)) := by
    rw [FinitePartialBijection.twoSidedDisagreement_comm]
  rw [FinitePartialBijection.trans_assoc] at htri₁ htri₂
  rw [houterR'] at htri₃
  have hmassL := D.middle_mass (D.improve f.1 g.1) hfgMem h.1 h.2
  have hmassR := D.middle_mass f.1 f.2 (D.improve g.1 h.1) hghMem
  unfold Near mass
  change 5 * (D.improve (D.improve f.1 g.1) h.1).twoSidedDisagreement
    (D.improve f.1 (D.improve g.1 h.1)) <
      4 * (Fintype.card (D.model W) + Fintype.card (D.model Z))
  omega

private theorem roundedComp_inv_left {X Y : I} (f : D.Rep X Y) :
    D.Near (roundedComp D (reversed D f) f)
      ⟨FinitePartialBijection.refl _, D.one_mem Y⟩ := by
  apply D.near_of_lt_far
  have hclose := D.improve_close f.1.symm (D.symm_mem f.1 f.2) f.1 f.2
  have hid := FinitePartialBijection.twoSidedDisagreement_reflOn_refl f.1.target
  have hself := D.self_small f.1 f.2
  have hmass := (D.endpoint_mass f.1 f.2).2
  have htri := FinitePartialBijection.twoSidedDisagreement_le
    (D.improve f.1.symm f.1) (f.1.symm.trans f.1)
      (FinitePartialBijection.refl (D.model Y))
  rw [f.1.symm_trans_self] at hclose htri
  rw [hid] at htri
  unfold Near mass
  change 5 * (D.improve f.1.symm f.1).twoSidedDisagreement
      (FinitePartialBijection.refl (D.model Y)) <
    4 * (Fintype.card (D.model Y) + Fintype.card (D.model Y))
  omega

private theorem roundedComp_inv_right {X Y : I} (f : D.Rep X Y) :
    D.Near (roundedComp D f (reversed D f))
      ⟨FinitePartialBijection.refl _, D.one_mem X⟩ := by
  apply D.near_of_lt_far
  have hclose := D.improve_close f.1 f.2 f.1.symm (D.symm_mem f.1 f.2)
  have hid := FinitePartialBijection.twoSidedDisagreement_reflOn_refl f.1.source
  have hself := D.self_small f.1 f.2
  have hmass := (D.endpoint_mass f.1 f.2).1
  have htri := FinitePartialBijection.twoSidedDisagreement_le
    (D.improve f.1 f.1.symm) (f.1.trans f.1.symm)
      (FinitePartialBijection.refl (D.model X))
  rw [f.1.trans_symm] at hclose htri
  rw [hid] at htri
  unfold Near mass
  change 5 * (D.improve f.1 f.1.symm).twoSidedDisagreement
      (FinitePartialBijection.refl (D.model X)) <
    4 * (Fintype.card (D.model X) + Fintype.card (D.model X))
  omega

/-- The finite groupoid presentation obtained from normalized partial-map
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

end FiniteNormalizedPartialClusterData
end NonsoficGroupsExist
