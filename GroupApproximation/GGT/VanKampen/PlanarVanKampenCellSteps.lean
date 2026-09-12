import GroupApproximation.GGT.VanKampen.PlanarVanKampenCellFactor
import GroupApproximation.GGT.VanKampen.CombMapEdgeDeletionEuler
import GroupApproximation.Meta.AxiomGuard

/-!
# Steps of the cellular planar van Kampen induction

The two small cases of the cellular planar van Kampen induction
(`PlanarVanKampenCells`), and the list bookkeeping of transporting factors.

* `exists_cellFactors_of_rotate`: factors for a rotated outer cycle give factors for
  the cycle itself.
* `exists_cellFactors_of_isolated_edge`: the one-edge map.
* `prod_map_snd_map_conj`, `map_fst_map_conj`: renaming the faces and conjugating the
  factors of a list.
-/

namespace GroupApproximation.GGT.VanKampen

open HullSC

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w}

/-- Renaming faces and conjugating factors conjugates the product. -/
theorem prod_map_snd_map_conj {α β : Type*} (φ : α → β) (T : G) :
    ∀ factors : List (α × G),
      ((factors.map fun y => (φ y.1, T * y.2 * T⁻¹)).map Prod.snd).prod =
        T * (factors.map Prod.snd).prod * T⁻¹
  | [] => by simp
  | y :: ys => by
      simp only [List.map_cons, List.prod_cons, prod_map_snd_map_conj φ T ys]
      group

/-- Renaming faces and conjugating factors renames the faces. -/
theorem map_fst_map_conj {α β : Type*} (φ : α → β) (T : G) :
    ∀ factors : List (α × G),
      (factors.map fun y => (φ y.1, T * y.2 * T⁻¹)).map Prod.fst =
        (factors.map Prod.fst).map φ
  | [] => rfl
  | y :: ys => by
      simp only [List.map_cons, map_fst_map_conj φ T ys]

/-- **Factors of a rotated outer cycle** give factors of the cycle. -/
theorem exists_cellFactors_of_rotate {M : CombMap.{v}}
    {label : M.Dart → RelLetter G Lambda} (lO : List M.Dart) {k : ℕ} (hk : k ≤ lO.length)
    (factors : List (M.Face × G)) (hfac : ∀ y ∈ factors, CellFactor M label y.1 y.2)
    (hprod : (factors.map Prod.snd).prod = RelLetter.listVal ((lO.rotate k).map label)) :
    ∃ factors' : List (M.Face × G), factors'.map Prod.fst = factors.map Prod.fst ∧
      (∀ y ∈ factors', CellFactor M label y.1 y.2) ∧
      (factors'.map Prod.snd).prod = RelLetter.listVal (lO.map label) := by
  refine ⟨factors.map fun y => (y.1, RelLetter.listVal ((lO.map label).take k) * y.2 *
    (RelLetter.listVal ((lO.map label).take k))⁻¹), map_fst_conj _ _, ?_, ?_⟩
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
    exact (hfac z hz).conj _
  · rw [prod_map_snd_conj, hprod, List.map_rotate,
      RelWord.listVal_rotate _ (by rw [List.length_map]; exact hk)]
    group

/-- **The isolated edge, cellularly.**  In a connected map made of one edge `a` on two
distinct faces, the outer face `faceOf a` reads the product of one cell factor for each
relator face. -/
theorem exists_cellFactors_of_isolated_edge {M : CombMap.{v}} (hM : M.IsConnected)
    (label : M.Dart → RelLetter G Lambda)
    (hlabel : ∀ d, label (M.alpha d) = RelWord.inv (label d)) {a : M.Dart}
    (hfa : M.facePerm a = a) (hfαa : M.facePerm (M.alpha a) = M.alpha a)
    (hcycα : M.IsFaceCycle [M.alpha a])
    (relFaces : Finset M.Face) (hOrel : M.faceOf a ∉ relFaces)
    (htriv : M.faceOf (M.alpha a) ∉ relFaces → RelLetter.listVal [label (M.alpha a)] = 1) :
    ∃ factors : List (M.Face × G), (factors.map Prod.fst).Nodup ∧
      (∀ f, f ∈ factors.map Prod.fst ↔ f ∈ relFaces) ∧
      (∀ y ∈ factors, CellFactor M label y.1 y.2) ∧
      (factors.map Prod.snd).prod = RelLetter.listVal [label a] := by
  classical
  have hσa : M.sigma a = M.alpha a := by
    rw [M.sigma_eq_facePerm_alpha, hfαa]
  have hσαa : M.sigma (M.alpha a) = a := by
    rw [M.sigma_eq_facePerm_alpha, M.alpha_involutive, hfa]
  have hall := M.dart_eq_or_alpha_of_swapped_endpoints hM a hσa hσαa
  have hfaces : ∀ f : M.Face, f = M.faceOf a ∨ f = M.faceOf (M.alpha a) := by
    intro f
    obtain ⟨d, rfl⟩ := Quotient.exists_rep f
    rcases hall d with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hvalα : RelLetter.listVal [label (M.alpha a)] = (RelLetter.listVal [label a])⁻¹ := by
    simp only [RelWord.listVal_cons, GGT.RelLetter.listVal_nil, mul_one, hlabel,
      RelWord.val_inv]
  by_cases hg : M.faceOf (M.alpha a) ∈ relFaces
  · refine ⟨[(M.faceOf (M.alpha a), (RelLetter.listVal [label (M.alpha a)])⁻¹)],
      List.nodup_singleton _, fun f => ?_, fun y hy => ?_, ?_⟩
    · simp only [List.map_cons, List.map_nil, List.mem_singleton]
      constructor
      · rintro rfl
        exact hg
      · intro hf
        rcases hfaces f with rfl | rfl
        · exact absurd hf hOrel
        · rfl
    · rw [List.mem_singleton] at hy
      subst hy
      exact (CellFactor.of_isFaceCycle (label := label) hcycα).inv
    · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hvalα,
        inv_inv]
  · refine ⟨[], List.nodup_nil, fun f => ?_, fun y hy => absurd hy List.not_mem_nil, ?_⟩
    · simp only [List.map_nil, List.not_mem_nil, false_iff]
      intro hf
      rcases hfaces f with rfl | rfl
      · exact hOrel hf
      · exact hg hf
    · have hone := htriv hg
      rw [hvalα, inv_eq_one] at hone
      rw [hone]
      rfl

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.exists_cellFactors_of_rotate
#audit_axioms GroupApproximation.GGT.VanKampen.exists_cellFactors_of_isolated_edge
