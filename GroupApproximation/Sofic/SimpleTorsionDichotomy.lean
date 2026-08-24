import GroupApproximation.Sofic.FiniteOrderNormalGenerator

/-!
# The simple torsion dichotomy

For a finitely generated countable simple group containing nontrivial torsion,
MF is equivalent to the existence of one operator-norm asymptotic model whose
normalized Hilbert--Schmidt ultraproduct separates every nonidentity element.
If the group is not MF, simplicity forces every norm-matrix-corona
homomorphism to be trivial.
-/

namespace GroupApproximation

open Filter

noncomputable section

variable {G : Type} [Group G]

/-- A single operator-norm asymptotic model separates every nonidentity
element after passage to one normalized-Hilbert--Schmidt ultraproduct. -/
def HasFaithfulOpToHSAsymptoticModel (G : Type) [Group G] : Prop :=
  ∃ (B : OpAlmostRepresentation G) (U : Ultrafilter ℕ)
    (hcof : (U : Filter ℕ) ≤ Filter.cofinite),
    Function.Injective
      ((KazhdanCompressionCore.toAsymptoticUnitaryRepresentation B).toUltraproductHom
        hcof)

/-- In a simple group, a normalized-HS ultraproduct model detecting one
nonidentity element is automatically faithful. -/
theorem faithful_opToHS_model_of_simple_of_detects
    [IsSimpleGroup G]
    (B : OpAlmostRepresentation G) (U : Ultrafilter ℕ)
    (hcof : (U : Filter ℕ) ≤ Filter.cofinite) {a : G}
    (hdetect :
      (KazhdanCompressionCore.toAsymptoticUnitaryRepresentation B).toUltraproductHom
        hcof a ≠ 1) :
    Function.Injective
      ((KazhdanCompressionCore.toAsymptoticUnitaryRepresentation B).toUltraproductHom
        hcof) := by
  let rho :=
    (KazhdanCompressionCore.toAsymptoticUnitaryRepresentation B).toUltraproductHom
      hcof
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal rho.ker inferInstance with
    hbot | htop
  · exact (MonoidHom.ker_eq_bot_iff rho).mp hbot
  · exfalso
    apply hdetect
    apply MonoidHom.mem_ker.mp
    rw [htop]
    exact Subgroup.mem_top a

/-- **Simple torsion dichotomy, positive side.**  A finitely generated
countable simple group containing a nonidentity finite-order element is MF
exactly when one operator-norm asymptotic model separates every nonidentity
element in normalized Hilbert--Schmidt norm. -/
theorem simple_torsion_isOperatorMF_iff_hasFaithfulOpToHSAsymptoticModel
    [Group.FG G] [IsSimpleGroup G]
    (htors : ∃ a : G, a ≠ 1 ∧ IsOfFinOrder a) :
    IsOperatorMF G ↔ HasFaithfulOpToHSAsymptoticModel G := by
  letI : Countable G := countable_of_fg (inferInstance : Group.FG G)
  constructor
  · intro hMF
    obtain ⟨a, ha, hfin⟩ := htors
    have hgen : Subgroup.normalClosure ({a} : Set G) = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
          (Subgroup.normalClosure ({a} : Set G)) inferInstance with hbot | htop
      · exfalso
        rw [Subgroup.normalClosure_eq_bot_iff] at hbot
        exact ha (Set.mem_singleton_iff.mp
          (hbot (Set.mem_singleton_iff.mpr rfl)))
      · exact htop
    have hnotNorm : a ∉ normMFResidual G := by
      rw [normMFResidual_eq_bot_of_isOperatorMF hMF]
      simpa using ha
    have hnotShadow : a ∉ opToHSShadowResidual G := by
      intro hshadow
      exact hnotNorm
        ((FiniteOrderNormalGenerator.finiteOrder_normalGenerator_mem_normMFResidual_iff_mem_opToHSShadowResidual
            hfin hgen).mpr hshadow)
    rw [mem_opToHSShadowResidual_iff] at hnotShadow
    push Not at hnotShadow
    obtain ⟨B, U, hcof, hdetect⟩ := hnotShadow
    exact ⟨B, U, hcof,
      faithful_opToHS_model_of_simple_of_detects B U hcof hdetect⟩
  · rintro ⟨B, U, hcof, hfaithful⟩
    apply (isOperatorMF_iff_normMFResidual_eq_bot (G := G)).mpr
    apply le_antisymm
    · intro g hg
      apply Subgroup.mem_bot.mpr
      apply hfaithful
      have hkill := (mem_opToHSShadowResidual_iff g).mp
        (normMFResidual_le_opToHSShadowResidual hg) B U hcof
      rw [map_one]
      exact hkill
    · exact bot_le

/-- **Simple torsion dichotomy, negative side.**  If such a group is not MF,
then every homomorphism to every norm-matrix corona is the trivial map. -/
theorem normMatrixCoronaHom_eq_one_of_simple_torsion_not_isOperatorMF
    [Group.FG G] [IsSimpleGroup G]
    (_htors : ∃ a : G, a ≠ 1 ∧ IsOfFinOrder a)
    (hnot : ¬ IsOperatorMF G) (X : ℕ → FiniteModel)
    (hX : ∀ n, 0 < Fintype.card (X n))
    (rho : G →* NormMatrixCoronaUnitary X) : rho = 1 := by
  letI : Countable G := countable_of_fg (inferInstance : Group.FG G)
  have htop : coronaMFResidual G = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (coronaMFResidual G) inferInstance with hbot | htop
    · exact absurd
        ((isOperatorMF_iff_coronaMFResidual_eq_bot (G := G)).mpr hbot) hnot
    · exact htop
  ext g
  have hg : g ∈ coronaMFResidual G := by
    rw [htop]
    exact Subgroup.mem_top g
  exact hg X hX rho

/-- The theorem-level dichotomy: the MF branch carries one faithful
operator-to-HS asymptotic model; the non-MF branch says all norm-corona
homomorphisms are trivial. -/
theorem simple_torsion_MF_or_all_corona_homs_trivial
    [Group.FG G] [IsSimpleGroup G]
    (htors : ∃ a : G, a ≠ 1 ∧ IsOfFinOrder a) :
    (IsOperatorMF G ∧ HasFaithfulOpToHSAsymptoticModel G) ∨
      (¬ IsOperatorMF G ∧
        ∀ (X : ℕ → FiniteModel) (_hX : ∀ n, 0 < Fintype.card (X n))
          (rho : G →* NormMatrixCoronaUnitary X), rho = 1) := by
  letI : Countable G := countable_of_fg (inferInstance : Group.FG G)
  by_cases hMF : IsOperatorMF G
  · exact Or.inl ⟨hMF,
      (simple_torsion_isOperatorMF_iff_hasFaithfulOpToHSAsymptoticModel htors).mp hMF⟩
  · exact Or.inr ⟨hMF, fun X hX rho ↦
      normMatrixCoronaHom_eq_one_of_simple_torsion_not_isOperatorMF
        htors hMF X hX rho⟩

end

end GroupApproximation
