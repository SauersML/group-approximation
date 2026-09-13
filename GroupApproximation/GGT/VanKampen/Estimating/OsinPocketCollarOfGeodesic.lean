import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPieces
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketTwoCollars
import GroupApproximation.GGT.VanKampen.Estimating.CyclicArcMap
import GroupApproximation.GGT.OsinGeodesicWord
import GroupApproximation.Meta.AxiomGuard

/-!
# The collar of a pocket carrier from the collar insertion

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the sides `s_1`, `s_2` of `Γ_1` are
replaced by geodesic words of the same values.  This module derives `PocketCollarStatement`
(`Estimating/OsinPocketPieces`) from the collar insertion `GeodesicCollarStatement` (lane
`kh-torsion`), through the two collars of `PocketRegion.exists_twoCollars_of_ne_or`.

* `allLettersRelGenSet`: the relative generating set whose base is all of `G` and whose
  subgroups are all of `G`.  Its base is inverse closed and every label is one of its letters,
  so the collar insertion applies to every diagram.  The collars still read geodesic words in
  the letters of `D`.
* `exists_collaredWord`: a geodesic word in the letters of `D` for every value.
* `Embedded.invDarts_map_of_alpha_comm`: a dart map commuting with `alpha` carries inverse dart
  lists.
* `pocketCollarStatement_of_geodesicCollar`: the collar.  A nondegenerate carrier has a nonempty
  arc or a side of value `≠ 1`, the hypothesis of the two collars.  The cells and arcs of the
  carrier are carried to the new diagram, and the sides become the collars, whose lengths are
  the norms of the old side values.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded HullSC WordMetric

/-- **Every letter admissible**: the relative generating set whose base is all of `G` and whose
subgroups are all `⊤`. -/
def allLettersRelGenSet (G : Type u) [Group G] (Lambda : Type w) : RelGenSet G Lambda where
  base := Set.univ
  fam := fun _ => ⊤
  symmetricGenerating :=
    ⟨fun x _ => Set.mem_union_left _ (Set.mem_univ x⁻¹),
      eq_top_iff.2 fun x _ => Subgroup.subset_closure (Set.mem_union_left _ (Set.mem_univ x))⟩

section Letters

variable {G : Type u} [Group G] {Lambda : Type w}

/-- The base of `allLettersRelGenSet` is inverse closed. -/
theorem allLettersRelGenSet_inv_mem (x : G) (_hx : x ∈ (allLettersRelGenSet G Lambda).base) :
    x⁻¹ ∈ (allLettersRelGenSet G Lambda).base :=
  Set.mem_univ x⁻¹

/-- Every letter is a letter of `allLettersRelGenSet`. -/
theorem allLettersRelGenSet_isLetter (l : RelLetter G Lambda) :
    (allLettersRelGenSet G Lambda).IsLetter l := by
  cases l with
  | base x => exact Set.mem_univ x
  | comp lam h => exact Subgroup.mem_top h

/-- **A geodesic word for every value**, in the letters of `D`. -/
theorem exists_collaredWord (D : RelGenSet G Lambda) (g : G) :
    ∃ word : List (RelLetter G Lambda), RelWord.IsAdmissible D word ∧
      RelLetter.listVal word = g ∧ word.length = wordNorm D.alphabet.carrier g := by
  obtain ⟨word, hletters, hvalue, hlength⟩ := GGT.OsinComponents.existsGeodesicWord D 1 g
  refine ⟨word, hletters, by simpa only [one_mul] using hvalue, ?_⟩
  rw [hlength, wordDist_one_left]

namespace Embedded

variable {W : Set (List (RelLetter G Lambda))}

/-- A dart map commuting with `alpha` carries inverse dart lists. -/
theorem invDarts_map_of_alpha_comm {Delta Delta' : DiscDiagram.{u, w, v} W}
    (f : Delta.toCombMap.Dart → Delta'.toCombMap.Dart)
    (halpha : ∀ d, Delta'.toCombMap.alpha (f d) = f (Delta.toCombMap.alpha d))
    (l : List Delta.toCombMap.Dart) :
    invDarts Delta' (l.map f) = (invDarts Delta l).map f := by
  simp only [invDarts, List.map_reverse, List.map_map]
  exact congrArg List.reverse (List.map_congr_left (fun d _ => halpha d))

end Embedded

end Letters

/-- **The collar from the collar insertion** (Osin Lemma 9.7(b)).  Let `K` be a nondegenerate
pocket carrier.  Take geodesic words `g₁`, `g₂` in the letters of `D` for the values of its
sides, empty when the side is, and insert both collars, in the letters of `allLettersRelGenSet`.
The new pocket reads `g₁ t₁ g₂ t₂`.  The cells `source` and `kept` and the arcs `t₁`, `t₂` are
carried along, and the sides, geodesic words for the old values, keep their bounds. -/
theorem pocketCollarStatement_of_geodesicCollar (hcollar : GeodesicCollarStatement.{u, w, v}) :
    PocketCollarStatement.{u, w, v} := by
  intro G _ Lambda D eps W X lo hi K hK
  obtain ⟨g₁, hadm₁, hval₁, hlen₁⟩ :=
    exists_collaredWord D (RelLetter.listVal (dartWord X K.firstSide))
  obtain ⟨g₂, hadm₂, hval₂, hlen₂⟩ :=
    exists_collaredWord D (RelLetter.listVal (dartWord X K.secondSide))
  have hnil₁ : K.firstSide = [] → g₁ = [] := fun h => by
    apply List.eq_nil_of_length_eq_zero
    rw [hlen₁, h]
    simp only [dartWord, RelLetter.listVal, List.map_nil, List.prod_nil, wordNorm_one]
  have hnil₂ : K.secondSide = [] → g₂ = [] := fun h => by
    apply List.eq_nil_of_length_eq_zero
    rw [hlen₂, h]
    simp only [dartWord, RelLetter.listVal, List.map_nil, List.prod_nil, wordNorm_one]
  have hne : invDarts X K.sourceArc.darts ≠ [] ∨ K.targetArc.darts ≠ [] ∨
      RelLetter.listVal (dartWord X K.firstSide) ≠ 1 ∨
        RelLetter.listVal (dartWord X K.secondSide) ≠ 1 := by
    rcases hK with h | h | h | h
    · refine Or.inl fun hnil => ?_
      have hlength : (invDarts X K.sourceArc.darts).length = K.sourceArc.length := by
        rw [invDarts, List.length_map, List.length_reverse, CyclicArc.darts_length]
      rw [hnil, List.length_nil] at hlength
      omega
    · refine Or.inr (Or.inl fun hnil => ?_)
      have hlength := CyclicArc.darts_length K.targetArc
      rw [hnil, List.length_nil] at hlength
      omega
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  obtain ⟨X', E, P'', c₁, c₂, ι, -, hin, hout, hdec, hword₁, hword₂, halpha, -, houter,
      hcells, hfaces⟩ :=
    PocketRegion.exists_twoCollars_of_ne_or hcollar (allLettersRelGenSet G Lambda)
      allLettersRelGenSet_inv_mem (fun _ => allLettersRelGenSet_isLetter _) K.pocket
      K.inner_follows K.outer_follows K.decomposition hne
      (fun l _ => allLettersRelGenSet_isLetter l) (fun l _ => allLettersRelGenSet_isLetter l)
      hval₁ hval₂ hnil₁ hnil₂
  have hsource : cellDarts X' (E.cellIndex K.source) = (cellDarts X K.source).map ι :=
    hcells K.source ((K.pocket.mem_outside_iff _).mpr K.source_not_mem)
  let K' : PocketCarrier D eps X' lo hi :=
    { pocket := P''
      inner_follows := hin
      outer_follows := hout
      source := E.cellIndex K.source
      source_not_mem := fun h => K.source_not_mem ((hfaces K.source).mp h)
      kept := E.cellIndex K.kept
      kept_mem := (hfaces K.kept).mpr K.kept_mem
      sourceArc := K.sourceArc.mapTo (⇑ι) hsource
      targetArc := K.targetArc.mapTo (⇑ι) houter
      firstSide := c₁
      secondSide := c₂
      decomposition := by
        rw [hdec, CyclicArc.mapTo_darts, CyclicArc.mapTo_darts,
          invDarts_map_of_alpha_comm (⇑ι) halpha]
      firstSide_length_le := by
        have h := congrArg List.length hword₁
        simp only [dartWord, List.length_map] at h
        rw [h, hlen₁]
        exact K.firstSide_norm_le
      secondSide_length_le := by
        have h := congrArg List.length hword₂
        simp only [dartWord, List.length_map] at h
        rw [h, hlen₂]
        exact K.secondSide_norm_le
      firstSide_norm_le := by
        rw [hword₁, hval₁]
        exact K.firstSide_norm_le
      secondSide_norm_le := by
        rw [hword₂, hval₂]
        exact K.secondSide_norm_le
      lo_le := by
        rw [CyclicArc.mapTo_start]
        exact K.lo_le
      le_hi := by
        rw [CyclicArc.mapTo_start, CyclicArc.mapTo_length]
        exact K.le_hi }
  refine ⟨X', K', ⟨E⟩, ?_⟩
  show RelWord.IsAdmissible D (dartWord X' c₁) ∧ RelWord.IsAdmissible D (dartWord X' c₂) ∧
    (dartWord X' c₁).length = wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X' c₁)) ∧
    (dartWord X' c₂).length = wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X' c₂))
  rw [hword₁, hword₂, hval₁, hval₂]
  exact ⟨hadm₁, hadm₂, hlen₁, hlen₂⟩

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.allLettersRelGenSet
#audit_axioms GroupApproximation.GGT.VanKampen.allLettersRelGenSet_inv_mem
#audit_axioms GroupApproximation.GGT.VanKampen.allLettersRelGenSet_isLetter
#audit_axioms GroupApproximation.GGT.VanKampen.exists_collaredWord
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.invDarts_map_of_alpha_comm
#audit_axioms GroupApproximation.GGT.VanKampen.pocketCollarStatement_of_geodesicCollar
