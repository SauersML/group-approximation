import GroupApproximation.Computability.AmalgamCode
import GroupApproximation.Computability.DirectProductCodeSemantics

/-!
# Semantics of the primitive-recursive amalgam code

The raw constructor is first identified with the presentation on the sum
alphabet having the two factor-relator families and exactly the displayed
edge relations.  Identification of this quotient with a particular pushout
is a separate theorem: it additionally needs semantic maps for the displayed
words and a generation hypothesis for the glued group.
-/

namespace GroupApproximation
namespace AmalgamCodeSemantics

open PresentationCodes PresentationCodeList PresentedGroupRelabel
open AmalgamCode RawWord

abbrev Raw : Type := AmalgamCode.Raw

abbrev codeRels (c : PresentationCode) :
    Set (FreeGroup (Fin (genCount c))) :=
  ((relatorFinset c : Finset (FreeGroup (Fin (genCount c)))) :
    Set (FreeGroup (Fin (genCount c))))

/-- Consecutive numbering of the two factor alphabets. -/
def amalgamGeneratorEquiv (c d : PresentationCode) (edges : List (Raw × Raw)) :
    Fin (genCount c) ⊕ Fin (genCount d) ≃
      Fin (genCount (amalgamCode c d edges)) :=
  finSumFinEquiv.trans (finCongr (amalgamCode_genCount c d edges).symm)

@[simp] theorem amalgamGeneratorEquiv_inl (c d : PresentationCode)
    (edges : List (Raw × Raw))
    (i : Fin (genCount c)) :
    amalgamGeneratorEquiv c d edges (Sum.inl i) =
      letterOf (amalgamCode c d edges) i := by
  apply Fin.ext
  simp only [amalgamGeneratorEquiv, Equiv.trans_apply,
    finSumFinEquiv_apply_left, finCongr_apply, Fin.val_cast, letterOf,
    amalgamCode_genCount]
  exact (Nat.mod_eq_of_lt
    (lt_of_lt_of_le i.isLt (Nat.le_add_right _ _))).symm

@[simp] theorem amalgamGeneratorEquiv_inr (c d : PresentationCode)
    (edges : List (Raw × Raw))
    (j : Fin (genCount d)) :
    amalgamGeneratorEquiv c d edges (Sum.inr j) =
      letterOf (amalgamCode c d edges) (genCount c + j) := by
  apply Fin.ext
  simp only [amalgamGeneratorEquiv, Equiv.trans_apply,
    finSumFinEquiv_apply_right, finCongr_apply, Fin.val_cast, letterOf,
    amalgamCode_genCount]
  exact (Nat.mod_eq_of_lt (Nat.add_lt_add_left j.isLt _)).symm

/-- The code reads a normalized left word as the left-summand word. -/
theorem wordOf_amalgamCode_leftWord (c d : PresentationCode)
    (edges : List (Raw × Raw)) (w : Raw) :
    wordOf (amalgamCode c d edges) (DirectProductCode.leftWord c w) =
      relabel (amalgamGeneratorEquiv c d edges)
        (FreeGroup.map Sum.inl (wordOf c w)) := by
  show FreeGroup.mk _ = _
  rw [wordOf, FreeGroup.map.mk, relabel, FreeGroup.map.mk]
  congr 1
  simp only [DirectProductCode.leftWord, List.map_map, Function.comp_def]
  refine List.map_congr_left fun p _ => ?_
  refine Prod.ext ?_ rfl
  rw [amalgamGeneratorEquiv_inl]
  simp only [letterOf]

/-- The code reads a shifted right word as the right-summand word. -/
theorem wordOf_amalgamCode_rightWord (c d : PresentationCode)
    (edges : List (Raw × Raw)) (w : Raw) :
    wordOf (amalgamCode c d edges) (DirectProductCode.rightWord c d w) =
      relabel (amalgamGeneratorEquiv c d edges)
        (FreeGroup.map Sum.inr (wordOf d w)) := by
  show FreeGroup.mk _ = _
  rw [wordOf, FreeGroup.map.mk, relabel, FreeGroup.map.mk]
  congr 1
  simp only [DirectProductCode.rightWord, List.map_map, Function.comp_def]
  refine List.map_congr_left fun p _ => ?_
  refine Prod.ext ?_ rfl
  rw [amalgamGeneratorEquiv_inr]
  simp only [letterOf]

/-- The semantic relation represented by one displayed raw pair. -/
def edgeRelator (c d : PresentationCode) (p : Raw × Raw) :
    FreeGroup (Fin (genCount c) ⊕ Fin (genCount d)) :=
  relabel Sum.inl (wordOf c p.1) *
    (relabel Sum.inr (wordOf d p.2))⁻¹

theorem wordOf_amalgamRelator (c d : PresentationCode)
    (edges : List (Raw × Raw)) (p : Raw × Raw) :
    wordOf (amalgamCode c d edges) (amalgamRelator c d p) =
      relabel (amalgamGeneratorEquiv c d edges) (edgeRelator c d p) := by
  simp only [amalgamRelator, wordOf_append, wordOf_invWord, edgeRelator,
    map_mul, map_inv, wordOf_amalgamCode_leftWord,
    wordOf_amalgamCode_rightWord, relabel]

/-- The exact semantic relator set written by `amalgamCode`. -/
def amalgamRels (c d : PresentationCode) (edges : List (Raw × Raw)) :
    Set (FreeGroup (Fin (genCount c) ⊕ Fin (genCount d))) :=
  (relabelRels Sum.inl (codeRels c) ∪
    relabelRels Sum.inr (codeRels d)) ∪
      edgeRelator c d '' {p | p ∈ edges}

theorem setOf_mem_append {alpha : Type} (A B : List alpha) :
    {x | x ∈ A ++ B} = {x | x ∈ A} ∪ {x | x ∈ B} := by
  ext x
  simp

theorem setOf_leftRelators (c d : PresentationCode)
    (edges : List (Raw × Raw)) :
    {x | x ∈ (c.2.map (DirectProductCode.leftWord c)).map
      (wordOf (amalgamCode c d edges))} =
      relabel (amalgamGeneratorEquiv c d edges) ''
        relabel Sum.inl '' codeRels c := by
  ext x
  constructor
  · intro hx
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    rw [wordOf_amalgamCode_leftWord]
    have hv' : wordOf c v ∈ codeRels c := by
      change wordOf c v ∈ relatorFinset c
      rw [relatorFinset, List.mem_toFinset]
      exact List.mem_map.mpr ⟨v, hv, rfl⟩
    exact ⟨_, ⟨_, hv', rfl⟩, rfl⟩
  · rintro ⟨_, ⟨_, hv, rfl⟩, rfl⟩
    simp only [codeRels, relatorFinset, Finset.mem_coe,
      List.mem_toFinset, List.mem_map] at hv
    obtain ⟨v, hv, rfl⟩ := hv
    exact List.mem_map.mpr ⟨DirectProductCode.leftWord c v,
      List.mem_map.mpr ⟨v, hv, rfl⟩,
      wordOf_amalgamCode_leftWord c d edges v⟩

theorem setOf_rightRelators (c d : PresentationCode)
    (edges : List (Raw × Raw)) :
    {x | x ∈ (d.2.map (DirectProductCode.rightWord c d)).map
      (wordOf (amalgamCode c d edges))} =
      relabel (amalgamGeneratorEquiv c d edges) ''
        relabel Sum.inr '' codeRels d := by
  ext x
  constructor
  · intro hx
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    rw [wordOf_amalgamCode_rightWord]
    have hv' : wordOf d v ∈ codeRels d := by
      change wordOf d v ∈ relatorFinset d
      rw [relatorFinset, List.mem_toFinset]
      exact List.mem_map.mpr ⟨v, hv, rfl⟩
    exact ⟨_, ⟨_, hv', rfl⟩, rfl⟩
  · rintro ⟨_, ⟨_, hv, rfl⟩, rfl⟩
    simp only [codeRels, relatorFinset, Finset.mem_coe,
      List.mem_toFinset, List.mem_map] at hv
    obtain ⟨v, hv, rfl⟩ := hv
    exact List.mem_map.mpr ⟨DirectProductCode.rightWord c d v,
      List.mem_map.mpr ⟨v, hv, rfl⟩,
      wordOf_amalgamCode_rightWord c d edges v⟩

theorem setOf_factorRelators (c d : PresentationCode)
    (edges : List (Raw × Raw)) :
    {x | x ∈ (factorWords c d).map (wordOf (amalgamCode c d edges))} =
      relabel (amalgamGeneratorEquiv c d edges) ''
        (relabelRels Sum.inl (codeRels c) ∪
          relabelRels Sum.inr (codeRels d)) := by
  rw [factorWords, List.map_append, setOf_mem_append, setOf_leftRelators,
    setOf_rightRelators]
  simp only [relabelRels, Set.image_union]

theorem setOf_edgeRelators (c d : PresentationCode)
    (edges : List (Raw × Raw)) :
    {x | x ∈ (edges.map (amalgamRelator c d)).map
      (wordOf (amalgamCode c d edges))} =
      relabel (amalgamGeneratorEquiv c d edges) ''
        (edgeRelator c d '' {p | p ∈ edges}) := by
  ext x
  constructor
  · intro hx
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw
    rw [wordOf_amalgamRelator]
    exact ⟨_, ⟨p, hp, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact List.mem_map.mpr ⟨amalgamRelator c d p,
      List.mem_map.mpr ⟨p, hp, rfl⟩,
      wordOf_amalgamRelator c d edges p⟩

/-- The raw relator list is exactly the relabelled sum-alphabet quotient. -/
theorem relSet_amalgamCode (c d : PresentationCode)
    (edges : List (Raw × Raw)) :
    {x | x ∈ relatorListOf (amalgamCode c d edges)} =
      relabelRels (amalgamGeneratorEquiv c d edges) (amalgamRels c d edges) := by
  rw [show relatorListOf (amalgamCode c d edges) =
      (factorWords c d ++ edges.map (amalgamRelator c d)).map
        (wordOf (amalgamCode c d edges)) by rfl]
  simp only [List.map_append]
  rw [setOf_mem_append, setOf_factorRelators, setOf_edgeRelators]
  simp only [amalgamRels, relabelRels, Set.image_union]

/-- The primitive-recursive raw code presents precisely the semantic quotient
by the displayed edge relations. -/
noncomputable def amalgamCodeEquivPresentation (c d : PresentationCode)
    (edges : List (Raw × Raw)) :
    Carrier (amalgamCode c d edges) ≃* PresentedGroup (amalgamRels c d edges) :=
  ((carrierEquivList (amalgamCode c d edges)).trans
      (presCongrSet (relSet_amalgamCode c d edges))).trans
    (congrEquiv (amalgamGeneratorEquiv c d edges) (amalgamRels c d edges)).symm

end AmalgamCodeSemantics
end GroupApproximation
