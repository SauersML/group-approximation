import GroupApproximation.Covers.TableCover
import GroupApproximation.Meta.AxiomGuard
import GroupApproximation.Sofic.Hyperlinear

/-!
# Finitely presented covers of non-hyperlinear groups

The finite multiplication-table presentation used for soficity is independent
of the target model class.  This file pulls a hyperlinear model of the presented
table back to the original table.  Consequently every finitely generated
non-hyperlinear group has a finitely presented non-hyperlinear cover.

This is the finite-dimensional unitary analogue of
`exists_finitelyPresented_cover_of_not_isSofic`.  It is useful even before an
example of a non-hyperlinear group is known: any future counterexample can be
replaced immediately by a finitely presented one.
-/

namespace GroupApproximation

universe u

variable {G : Type u} [Group G]

/-- Restrict a hyperlinear model to a smaller finite test set. -/
noncomputable def HyperlinearModel.restrictTable
    {F F' : Finset G} {ε : ℝ} (M : HyperlinearModel G F' ε)
    (hFF : F ⊆ F') : HyperlinearModel G F ε where
  carrier := M.carrier
  nonempty := M.nonempty
  map := M.map
  isUnitary := M.isUnitary
  multiplicative g hg h hh := M.multiplicative g (hFF hg) h (hFF hh)
  separated g hg h hh hne := M.separated g (hFF hg) h (hFF hh) hne

/-- A forbidden hyperlinear table stays forbidden after adjoining more named
elements. -/
theorem hyperlinearModel_isEmpty_mono {F F' : Finset G} {ε : ℝ}
    (hbad : IsEmpty (HyperlinearModel G F ε)) (hFF : F ⊆ F') :
    IsEmpty (HyperlinearModel G F' ε) := by
  constructor
  intro M
  exact hbad.false (M.restrictTable hFF)

/-- Pull a hyperlinear model of the finitely presented table group back to a
model of the original finite table. -/
noncomputable def pullbackHyperlinearModel (F : Finset G) (h₁ : 1 ∈ F) {ε : ℝ}
    (M : HyperlinearModel (tableGroup F h₁) (tableTestSet F h₁) ε) :
    HyperlinearModel G F ε := by
  classical
  refine
    { carrier := M.carrier
      nonempty := M.nonempty
      map := fun g ↦ if hg : g ∈ multiplicationTable F then
        M.map (tableGenerator F h₁ ⟨g, hg⟩) else 1
      isUnitary := ?_
      multiplicative := ?_
      separated := ?_ }
  · intro g
    by_cases hg : g ∈ multiplicationTable F
    · simpa [hg] using M.isUnitary (tableGenerator F h₁ ⟨g, hg⟩)
    · simp [hg]
  · intro g hg h hh
    have hgDomain : g ∈ multiplicationTable F :=
      mem_multiplicationTable_of_mem F hg
    have hhDomain : h ∈ multiplicationTable F :=
      mem_multiplicationTable_of_mem F hh
    have hmulDomain : g * h ∈ multiplicationTable F :=
      mul_mem_multiplicationTable F hg hh
    let xg := tableGenerator F h₁ ⟨g, hgDomain⟩
    let xh := tableGenerator F h₁ ⟨h, hhDomain⟩
    have hxg : xg ∈ tableTestSet F h₁ :=
      tableGenerator_mem_tableTestSet F h₁ hg
    have hxh : xh ∈ tableTestSet F h₁ :=
      tableGenerator_mem_tableTestSet F h₁ hh
    simp only [dif_pos hgDomain, dif_pos hhDomain, dif_pos hmulDomain]
    have hgen : tableGenerator F h₁ ⟨g * h, hmulDomain⟩ = xg * xh :=
      (tableGenerator_mul F h₁ hg hh).symm
    rw [hgen]
    exact M.multiplicative xg hxg xh hxh
  · intro g hg h hh hne
    have hgDomain : g ∈ multiplicationTable F :=
      mem_multiplicationTable_of_mem F hg
    have hhDomain : h ∈ multiplicationTable F :=
      mem_multiplicationTable_of_mem F hh
    simp only [dif_pos hgDomain, dif_pos hhDomain]
    exact M.separated _ (tableGenerator_mem_tableTestSet F h₁ hg) _
      (tableGenerator_mem_tableTestSet F h₁ hh)
      (tableGenerator_ne F h₁ hgDomain hhDomain hne)

/-- A forbidden hyperlinear table presents a finitely presented group whose
corresponding named table is still forbidden. -/
theorem tableGroup_no_hyperlinearModel (F : Finset G) (h₁ : 1 ∈ F) {ε : ℝ}
    (hbad : IsEmpty (HyperlinearModel G F ε)) :
    IsEmpty (HyperlinearModel (tableGroup F h₁) (tableTestSet F h₁) ε) := by
  constructor
  intro M
  exact hbad.false (pullbackHyperlinearModel F h₁ M)

/-- The table group of a forbidden positive-accuracy hyperlinear table is not
hyperlinear. -/
theorem tableGroup_not_isHyperlinear (F : Finset G) (h₁ : 1 ∈ F) {ε : ℝ}
    (hε : 0 < ε) (hbad : IsEmpty (HyperlinearModel G F ε)) :
    ¬ IsHyperlinear (tableGroup F h₁) := by
  intro hhyperlinear
  obtain ⟨M⟩ := hhyperlinear (tableTestSet F h₁) ε hε
  exact (tableGroup_no_hyperlinearModel F h₁ hbad).false M

/-- Failure of hyperlinearity is witnessed by one finite table at one positive
accuracy.  The table is enlarged to contain the identity for the presentation
constructor. -/
theorem exists_hyperlinearTable_obstruction (h : ¬ IsHyperlinear G) :
    ∃ (F : Finset G) (ε : ℝ), 1 ∈ F ∧ 0 < ε ∧
      IsEmpty (HyperlinearModel G F ε) := by
  classical
  by_contra hcon
  push Not at hcon
  apply h
  intro F ε hε
  have hone : (1 : G) ∈ insert 1 F := Finset.mem_insert_self 1 F
  obtain ⟨M⟩ := hcon (insert 1 F) ε hone hε
  exact ⟨M.restrictTable (Finset.subset_insert 1 F)⟩

/-- **Finite-presentation reduction for hyperlinearity.**  Every finitely
generated non-hyperlinear group is a quotient of a finitely presented
non-hyperlinear group. -/
theorem exists_finitelyPresented_cover_of_not_isHyperlinear [Group.FG G]
    (h : ¬ IsHyperlinear G) :
    ∃ (H : Type u) (_ : Group H), Group.IsFinitelyPresented H ∧
      ¬ IsHyperlinear H ∧ ∃ π : H →* G, Function.Surjective π := by
  classical
  obtain ⟨F₀, ε, _, hε, hbad₀⟩ := exists_hyperlinearTable_obstruction h
  obtain ⟨_, S, _, hgen⟩ := Group.fg_iff'.mp (inferInstance : Group.FG G)
  let F : Finset G := insert 1 (F₀ ∪ S)
  have h₁ : (1 : G) ∈ F := by simp [F]
  have hF₀ : F₀ ⊆ F := by
    intro g hg
    simp [F, hg]
  have hS : S ⊆ F := by
    intro g hg
    simp [F, hg]
  have hbadF : IsEmpty (HyperlinearModel G F ε) :=
    hyperlinearModel_isEmpty_mono hbad₀ hF₀
  have hnHyperlinear : ¬ IsHyperlinear (tableGroup F h₁) :=
    tableGroup_not_isHyperlinear F h₁ hε hbadF
  have hsurj : Function.Surjective (tableEvaluation F h₁) :=
    tableEvaluation_surjective F h₁ S hS hgen
  letI : Group.IsFinitelyPresented (tableGroup F h₁) := inferInstance
  exact ⟨tableGroup F h₁, inferInstance, inferInstance, hnHyperlinear,
    tableEvaluation F h₁, hsurj⟩

/-- In particular, existence of any finitely generated non-hyperlinear group
implies existence of a finitely presented one. -/
theorem exists_finitelyPresented_not_isHyperlinear [Group.FG G]
    (h : ¬ IsHyperlinear G) :
    ∃ (H : Type u) (_ : Group H), Group.IsFinitelyPresented H ∧
      ¬ IsHyperlinear H := by
  obtain ⟨H, _, hfp, hn, _⟩ :=
    exists_finitelyPresented_cover_of_not_isHyperlinear h
  exact ⟨H, inferInstance, hfp, hn⟩

/-- Every non-hyperlinear group already has a finitely generated
non-hyperlinear subgroup.  This is the contrapositive of the finite-subgroup
locality theorem for hyperlinearity. -/
theorem exists_finitelyGenerated_subgroup_not_isHyperlinear
    (h : ¬ IsHyperlinear G) :
    ∃ H : Subgroup G, Group.FG H ∧ ¬ IsHyperlinear H := by
  classical
  by_contra hcon
  push Not at hcon
  apply h
  apply isHyperlinear_of_local
  intro F
  let H : Subgroup G := Subgroup.closure (F : Set G)
  have hHfg : Group.FG H :=
    (Group.fg_iff_subgroup_fg H).mpr
      ((Subgroup.fg_iff H).mpr ⟨(F : Set G), rfl, F.finite_toSet⟩)
  refine ⟨H, inferInstance, H.subtype, H.subtype_injective,
    hcon H hHfg, ?_⟩
  intro g hg
  exact ⟨⟨g, Subgroup.subset_closure hg⟩, rfl⟩

/-- **Existence equivalence.**  A non-hyperlinear group exists exactly when a
finitely presented non-hyperlinear group exists.  The forward implication is
constructive at the level of groups once a counterexample is supplied: take a
finitely generated bad subgroup and then its finite table cover. -/
theorem exists_not_isHyperlinear_iff_exists_finitelyPresented :
    (∃ (G : Type u) (_ : Group G), ¬ IsHyperlinear G) ↔
      ∃ (H : Type u) (_ : Group H), Group.IsFinitelyPresented H ∧
        ¬ IsHyperlinear H := by
  constructor
  · rintro ⟨G, _, hG⟩
    obtain ⟨K, hKfg, hK⟩ :=
      exists_finitelyGenerated_subgroup_not_isHyperlinear hG
    letI : Group.FG K := hKfg
    exact exists_finitelyPresented_not_isHyperlinear hK
  · rintro ⟨H, _, _, hH⟩
    exact ⟨H, inferInstance, hH⟩

end GroupApproximation

open GroupApproximation

#audit_axioms exists_finitelyPresented_cover_of_not_isHyperlinear
#audit_axioms exists_finitelyGenerated_subgroup_not_isHyperlinear
#audit_axioms exists_not_isHyperlinear_iff_exists_finitelyPresented
