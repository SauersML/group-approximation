import GroupApproximation.Sofic.LiteralAffineFreeProductBassSerre
import GroupApproximation.Sofic.AvatarWordFamily

/-!
# Avatar blueprint over the amplified affine-congruence source

The rejected literal affine avatar blueprint used long words in two abstract
defect letters.  Each expanded defect word consequently occurred several
times in a tying relator; the resulting multiplicity inequalities are
incompatible with aperiodicity and `C'(1/8)`.

Here the source is instead the torsion-free free-product amplification of the
affine-congruence HNN envelope.  Its normal defect contains an explicit
crossing element and a conjugate of that element.  We use those two elements
as the designated defect basis and use the singleton abstract words `a` and
`b` as ties.  Thus each expanded defect word occurs exactly once in its own
tying relator.  This removes the proved multiplicity obstruction; it does not
assert the separate finite overlap checks required by `AvatarRouterInstance`.
-/

namespace GroupApproximation
namespace LiteralAffineFreeProductAvatarBlueprint

open scoped commutatorElement
open LiteralAffineCongruenceSource
open LiteralAffineFreeProductSource
open LiteralAffineFreeProductBassSerre
open BespokeRouter
open BespokeRouter.AvatarWordFamily

noncomputable section

/-- The amplified, torsion-free bare defect source. -/
noncomputable abbrev source := amplifiedDefectData

/-- A finite word presentation of the amplified source ambient. -/
noncomputable def sourceWordPresentation : WordPresentation Ambient := by
  letI : Group.IsFinitelyPresented Ambient := ambient_isFinitelyPresented
  exact wordPresentation Ambient

/-- Removing the empty relator does not change the presented normal subgroup.
This normalization is necessary before any occurrence marker can be selected:
the empty router word has no cyclic position at all. -/
def withoutEmptyRelators {G : Type} [Group G]
    (P : WordPresentation G) : WordPresentation G where
  card := P.card
  hom := P.hom
  hom_surjective := P.hom_surjective
  rel := {r | r ∈ P.rel ∧ r ≠ []}
  rel_finite := P.rel_finite.subset fun _ hr ↦ hr.1
  ker_le := by
    intro x hx
    have hle : wordSubgroup P.rel ≤ wordSubgroup {r | r ∈ P.rel ∧ r ≠ []} := by
      refine Subgroup.normalClosure_le_normal ?_
      rintro _ ⟨r, hr, rfl⟩
      by_cases hnil : r = []
      · subst r
        rw [← FreeGroup.one_eq_mk]
        exact one_mem _
      · exact mem_wordSubgroup ⟨hr, hnil⟩
    exact hle (P.ker_le hx)

/-- Its unconditional positive Tietze transform, normalized to contain no
empty relator. -/
noncomputable def sourcePositiveWordPresentation : WordPresentation Ambient := by
  letI : Group.IsFinitelyPresented Ambient := ambient_isFinitelyPresented
  exact withoutEmptyRelators
    (PositivePresentation.presentation sourceWordPresentation)

/-- A positive name for an element of the amplified ambient. -/
noncomputable def sourcePositiveName (g : Ambient) :
    List (Fin sourcePositiveWordPresentation.card × Bool) := by
  letI : Group.IsFinitelyPresented Ambient := ambient_isFinitelyPresented
  exact PositivePresentation.name sourceWordPresentation g

theorem sourcePositiveName_positive (g : Ambient) :
    ∀ c ∈ sourcePositiveName g, c.2 = true := by
  letI : Group.IsFinitelyPresented Ambient := ambient_isFinitelyPresented
  exact PositivePresentation.name_positive sourceWordPresentation g

theorem sourcePositiveName_spec (g : Ambient) :
    sourcePositiveWordPresentation.hom (FreeGroup.mk (sourcePositiveName g)) = g := by
  letI : Group.IsFinitelyPresented Ambient := ambient_isFinitelyPresented
  exact PositivePresentation.presentation_hom_name sourceWordPresentation g

theorem sourcePositiveName_ne_nil {g : Ambient} (hg : g ≠ 1) :
    sourcePositiveName g ≠ [] := by
  intro hnil
  apply hg
  rw [← sourcePositiveName_spec g, hnil]
  rw [← FreeGroup.one_eq_mk, map_one]

/-- A left-factor conjugator separating two crossing defect elements. -/
def basisConjugator : Ambient := markedDefect ^ 2

/-- The second designated defect element is a conjugate of the crossing one. -/
def conjugateCrossing : Ambient :=
  basisConjugator * crossingDefect * basisConjugator⁻¹

theorem conjugateCrossing_mem :
    conjugateCrossing ∈ source.core.defectNormal :=
  (inferInstance : source.core.defectNormal.Normal).conj_mem
    crossingDefect crossingDefect_mem basisConjugator

theorem conjugateCrossing_ne_one : conjugateCrossing ≠ 1 := by
  intro h
  apply crossingDefect_ne_one
  have hconj :
      basisConjugator⁻¹ * conjugateCrossing * basisConjugator =
        crossingDefect := by
    unfold conjugateCrossing
    group
  calc
    crossingDefect =
        basisConjugator⁻¹ * conjugateCrossing * basisConjugator := hconj.symm
    _ = 1 := by rw [h]; simp

/-- Singleton ties: no expanded defect word is repeated inside either tie. -/
def tieDefectWord : Fin 2 → List (Fin 2 × Bool)
  | 0 => [((0 : Fin 2), true)]
  | 1 => [((1 : Fin 2), true)]

theorem tieDefectWord_positive (i : Fin 2) :
    ∀ c ∈ tieDefectWord i, c.2 = true := by
  fin_cases i <;> simp [tieDefectWord]

/-- The amplified source half of the replacement blueprint. -/
noncomputable def sourceData :
    SourceData Ambient source.core.defectNormal source.s where
  pres := sourcePositiveWordPresentation
  rel_positive := by
    letI : Group.IsFinitelyPresented Ambient := ambient_isFinitelyPresented
    intro r hr
    exact PositivePresentation.presentation_rel_positive sourceWordPresentation r hr.1
  basisOneWord := sourcePositiveName crossingDefect
  basisTwoWord := sourcePositiveName conjugateCrossing
  basisOneWord_positive := sourcePositiveName_positive crossingDefect
  basisTwoWord_positive := sourcePositiveName_positive conjugateCrossing
  basisOne_mem := by
    rw [sourcePositiveName_spec]
    exact crossingDefect_mem
  basisTwo_mem := by
    rw [sourcePositiveName_spec]
    exact conjugateCrossing_mem
  protectedSrcWord := sourcePositiveName source.s
  protectedSrcWord_spec := sourcePositiveName_spec source.s
  tieDefectWord := tieDefectWord
  tieDefectWord_positive := tieDefectWord_positive

theorem sourceData_basisOneWord_ne_nil : sourceData.basisOneWord ≠ [] :=
  sourcePositiveName_ne_nil crossingDefect_ne_one

theorem sourceData_basisTwoWord_ne_nil : sourceData.basisTwoWord ≠ [] :=
  sourcePositiveName_ne_nil conjugateCrossing_ne_one

/-- The first concrete level-three unipotent used by the partner tie. -/
def gamma3WitnessElement : CongruenceSubgroup.gamma3Partner.B :=
  ⟨CongruenceTorsionFree.gamma3Witness,
    CongruenceTorsionFree.gamma3Witness_mem⟩

/-- The second level-three unipotent, in the adjacent root subgroup. -/
def gamma3Witness23 : CongruenceSubgroup.SL3Z :=
  ⟨!![1, 0, 0; 0, 1, 3; 0, 0, 1], by decide⟩

theorem gamma3Witness23_mem : gamma3Witness23 ∈ CongruenceSubgroup.gamma3 := by
  refine CongruenceTorsionFree.mem_congruenceSubgroupThree.mpr fun i j ↦ ?_
  fin_cases i <;> fin_cases j <;> decide

/-- The second explicit partner element. -/
def gamma3WitnessElement23 : CongruenceSubgroup.gamma3Partner.B :=
  ⟨gamma3Witness23, gamma3Witness23_mem⟩

/-- The partner ties do not collapse to a cyclic image. -/
theorem gamma3WitnessElements_not_commute :
    ¬ Commute gamma3WitnessElement gamma3WitnessElement23 := by
  change ¬ Commute
    (⟨CongruenceTorsionFree.gamma3Witness,
      CongruenceTorsionFree.gamma3Witness_mem⟩ : ↥CongruenceSubgroup.gamma3)
    (⟨gamma3Witness23, gamma3Witness23_mem⟩ : ↥CongruenceSubgroup.gamma3)
  intro h
  have hm := congrArg
    (fun A : ↥CongruenceSubgroup.gamma3 ↦
      (((A.1 : CongruenceSubgroup.SL3Z) : Matrix (Fin 3) (Fin 3) ℤ) 0 2)) h.eq
  simp only [gamma3Witness23, CongruenceTorsionFree.gamma3Witness] at hm
  set_option maxRecDepth 10000 in
    change (9 : ℤ) = 0 at hm
  omega

/-- The concrete noncommuting pair consumed by `gamma3PartnerData`. -/
def gamma3TieElements : Fin 2 → CongruenceSubgroup.gamma3Partner.B
  | 0 => gamma3WitnessElement
  | 1 => gamma3WitnessElement23

/-- The certified partner data with the same harmless empty-relator
normalization as the source presentation. -/
noncomputable def gamma3NonemptyPartnerData :
    PartnerData CongruenceSubgroup.gamma3Partner.B where
  pres := withoutEmptyRelators gamma3PositiveWordPresentation
  rel_positive := by
    intro r hr
    exact PositivePresentation.presentation_rel_positive
      gamma3WordPresentation r hr.1
  tiePartnerWord := fun i ↦
    PositivePresentation.name gamma3WordPresentation (gamma3TieElements i)
  tiePartnerWord_positive := fun i ↦
    PositivePresentation.name_positive gamma3WordPresentation (gamma3TieElements i)

/-- The replacement blueprint, using the existing certified noncommuting
`Gamma(3)` partner pair. -/
noncomputable def blueprint :
    Blueprint Ambient source.core.defectNormal source.s
      CongruenceSubgroup.gamma3Partner.B where
  src := sourceData
  par := gamma3NonemptyPartnerData

theorem blueprint_basis_ne_nil (k : Fin 2) :
    1 ≤ (blueprint.basisWord k).length := by
  fin_cases k
  · exact List.length_pos_iff.mpr sourceData_basisOneWord_ne_nil
  · exact List.length_pos_iff.mpr sourceData_basisTwoWord_ne_nil

/-- Exact shape of the new defect ties.  In contrast to the rejected literal
ties, the suffix is one expanded basis word, not a word with multiplicities. -/
theorem blueprint_defectTieWord (i : Fin 2) :
    blueprint.defectTieWord i =
      [((i : Fin 2), true)] ++ blueprint.defectAvatarWord i := by
  fin_cases i
  · change [((0 : Fin 2), true)] ++
      avatarSubst blueprint.defectAvatarWord [((0 : Fin 2), true)] = _
    rw [avatarSubst_cons, avatarSubst_nil]
    simp [avatarSubstLetter]
  · change [((1 : Fin 2), true)] ++
      avatarSubst blueprint.defectAvatarWord [((1 : Fin 2), true)] = _
    rw [avatarSubst_cons, avatarSubst_nil]
    simp [avatarSubstLetter]

/-- Consequently the tie length is exactly one plus the selected expanded
defect word's length. -/
theorem length_blueprint_defectTieWord (i : Fin 2) :
    (blueprint.defectTieWord i).length =
      1 + (blueprint.defectAvatarWord i).length := by
  rw [blueprint_defectTieWord]
  simp [Nat.add_comm]

/-- Finiteness gives an unconditional strict ceiling on every piece in the
amplified router family.  The separate metric task is to make this ceiling at
most one eighth of the shortest relator; arbitrary chosen presentations do not
supply that ratio. -/
theorem exists_blueprint_piece_length_ceiling :
    ∃ C : ℕ, ∀ p,
      SmallCancellationRouter.IsPiece
        (SmallCancellationRouter.symmetrization blueprint.relators) p →
      p.length < C :=
  SmallCancellationRouter.exists_piece_length_ceiling blueprint.relators_finite

/-- The protected avatar has exactly the unreduced substitution length.  Both
the chosen source name and every avatar are positive, so no free reduction is
lost at an avatar seam.  This turns the protected-ball input into a concrete
arithmetic bound on the chosen positive source name. -/
theorem blueprint_protected_norm :
    FreeGroup.norm (FreeGroup.lift blueprint.srcAvatar blueprint.protectedWord) =
      (sourcePositiveName source.s).length * blueprint.avatarLength := by
  let w := sourcePositiveName source.s
  let out := avatarSubst blueprint.srcAvatarWord w
  have hwpos : ∀ c ∈ w, c.2 = true := sourcePositiveName_positive source.s
  have hapos : ∀ k, ∀ c ∈ blueprint.srcAvatarWord k, c.2 = true :=
    fun k ↦ forall_positive_avatarWord blueprint.avatarCount blueprint.codeL (k : ℕ)
  have houtpos : ∀ c ∈ out, c.2 = true :=
    forall_positive_avatarSubst blueprint.srcAvatarWord hapos hwpos
  have houtlen : out.length = w.length * blueprint.avatarLength :=
    length_avatarSubst_eq blueprint.srcAvatarWord blueprint.avatarLength
      blueprint.length_srcAvatarWord w
  change FreeGroup.norm
      (FreeGroup.lift blueprint.srcAvatar (FreeGroup.mk w)) =
        w.length * blueprint.avatarLength
  rw [lift_mk_eq_mk_avatarSubst blueprint.srcAvatarWord blueprint.srcAvatar
    (fun _ ↦ rfl) w]
  change (FreeGroup.mk out).toWord.length = w.length * blueprint.avatarLength
  rw [AvatarMetricCheck.toWord_mk_of_forall_positive houtpos, houtlen]

/-- The protected avatar remains nontrivial after amplification. -/
theorem blueprint_protectedWord_ne_one :
    FreeGroup.lift blueprint.srcAvatar blueprint.protectedWord ≠ 1 := by
  intro hone
  have hnorm := blueprint_protected_norm
  rw [hone] at hnorm
  have hwpos : 0 < (sourcePositiveName source.s).length :=
    List.length_pos_iff.mpr (sourcePositiveName_ne_nil source.s_ne_one)
  have havpos : 0 < blueprint.avatarLength :=
    lt_of_lt_of_le (by decide) blueprint.sixteen_le_avatarLength
  have hprod : 0 <
      (sourcePositiveName source.s).length * blueprint.avatarLength :=
    Nat.mul_pos hwpos havpos
  simp only [FreeGroup.norm_one] at hnorm
  exact (Nat.ne_of_gt hprod) hnorm.symm

end

end LiteralAffineFreeProductAvatarBlueprint
end GroupApproximation
