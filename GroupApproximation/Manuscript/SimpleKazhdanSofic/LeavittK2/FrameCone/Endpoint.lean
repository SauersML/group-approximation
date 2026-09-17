import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.Transfer
import GroupApproximation.Meta.AxiomGuard

/-!
# Frame cone at rank four (Khanh Prop. 4.2, `k ≤ 2`)

Khanh (arXiv:2609.08428), Prop. `prop:frame-cone`:

> Let `E` be a finite set of frames of lengths `k_i ≤ r-2` in `L^r`. Then there is `v ∈ L^r`
> such that `(v, f_i)` is a frame for every `i ∈ E`.

Here `r = 4`, `L = L_{F_2}(1,2)`. Route: a frame `f_i` is a unit `U_i` with
`U_i d_j = Φ⁻¹ f_{i,j}` (`unit_of_frame`); `a_i = t_{1^{k_i}} U_i⁻¹ ≠ 0` because
`a_i U_i s_{1^{k_i}} = 1`; the word multiplier (lane 08, `WordMultiplierStatement`) gives `x`
and `η_i ≠ []` with `η_i^* a_i x = 1`; `cone_core` gives `W_i` with `W_i d_0 = U_i⁻¹ x` and
`W_i d_{j+1} = d_j`; then `U_i W_i` carries the leaves to `(Φ x, f_i)` (`frame_of_unit`).

The endpoints here are `_of_` reductions to `WordMultiplierStatement` (Khanh Lemma
`lem:word-multiplier`); lane 08 discharges it in `FrameCone/Main.lean` (`frame_cone_four`).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone

open GroupApproximation

/-- **Frame cone, finite family indexed by `Fin s`**, from the word multiplier. -/
theorem frame_cone_four_fin_of_wordMultiplier (h : WordMultiplierStatement) (s : ℕ)
    (f : Fin s → List (Fin 4 → BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)))
    (hf : ∀ i, (f i).length ≤ 2 ∧ IsFrame (f i)) :
    ∃ v, ∀ i, IsFrame (v :: f i) := by
  choose U hU using fun i => unit_of_frame (BinaryLeavitt.family (ZMod 2)) (hf i).2
  have ha : ∀ i, (BinaryLeavitt.family (ZMod 2)).wordT (List.replicate (f i).length 1) *
      ((U i)⁻¹ : (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))ˣ) ≠ 0 := by
    intro i hai
    have h1 : (BinaryLeavitt.family (ZMod 2)).wordT (List.replicate (f i).length 1) *
        (BinaryLeavitt.family (ZMod 2)).wordS (List.replicate (f i).length 1) = 0 := by
      calc
        (BinaryLeavitt.family (ZMod 2)).wordT (List.replicate (f i).length 1) *
            (BinaryLeavitt.family (ZMod 2)).wordS (List.replicate (f i).length 1) =
            (BinaryLeavitt.family (ZMod 2)).wordT (List.replicate (f i).length 1) *
              (((U i)⁻¹ : (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))ˣ) *
                ((U i : BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) *
                  (BinaryLeavitt.family (ZMod 2)).wordS (List.replicate (f i).length 1))) := by
          rw [Units.inv_mul_cancel_left]
        _ = 0 := by
          rw [← mul_assoc, hai, zero_mul]
    exact one_ne_zero
      (((BinaryLeavitt.family (ZMod 2)).wordT_mul_wordS_self _).symm.trans h1)
  obtain ⟨x, η, hη, hx⟩ := h s
    (fun i => (BinaryLeavitt.family (ZMod 2)).wordT (List.replicate (f i).length 1) *
      ((U i)⁻¹ : (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))ˣ)) ha
  refine ⟨scalarToVec (BinaryLeavitt.family (ZMod 2)) x, fun i => ?_⟩
  have hp := hx i
  simp only [mul_assoc] at hp
  have hlen := (hf i).1
  obtain ⟨W, hW0, hWs⟩ := cone_core (BinaryLeavitt.family (ZMod 2)) (f i).length hlen (η i)
    (hη i) _ hp
  refine frame_of_unit (BinaryLeavitt.family (ZMod 2)) (by rw [List.length_cons]; omega)
    (U i * W) ?_
  rintro ⟨jv, hjv⟩ hj
  cases jv with
  | zero =>
      have hW0' : (W : BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) *
          (BinaryLeavitt.family (ZMod 2)).wordS (leftCombWord 3 ⟨0, hjv⟩) =
            ((U i)⁻¹ : (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))ˣ) * x := hW0
      show ((U i : BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) * W) *
          (BinaryLeavitt.family (ZMod 2)).wordS (leftCombWord 3 ⟨0, hjv⟩) =
        vecToScalar (BinaryLeavitt.family (ZMod 2))
          (scalarToVec (BinaryLeavitt.family (ZMod 2)) x)
      rw [mul_assoc, hW0', Units.mul_inv_cancel_left, vecToScalar_scalarToVec]
  | succ m =>
      have hm : m < (f i).length := Nat.lt_of_succ_lt_succ hj
      show ((U i : BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) * W) *
          (BinaryLeavitt.family (ZMod 2)).wordS (leftCombWord 3 ⟨m + 1, hjv⟩) =
        vecToScalar (BinaryLeavitt.family (ZMod 2)) ((f i)[m]'hm)
      rw [mul_assoc, hWs m hm]
      exact hU i ⟨m, by omega⟩ hm

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.frame_cone_four_fin_of_wordMultiplier

/-- **Frame cone, list form**, from the word multiplier. -/
theorem frame_cone_four_list_of_wordMultiplier (h : WordMultiplierStatement)
    (F : List (List (Fin 4 → BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))))
    (hF : ∀ f ∈ F, f.length ≤ 2 ∧ IsFrame f) :
    ∃ v, ∀ f ∈ F, IsFrame (v :: f) := by
  obtain ⟨v, hv⟩ := frame_cone_four_fin_of_wordMultiplier h F.length (fun i => F.get i)
    (fun i => hF _ (List.get_mem F i))
  refine ⟨v, fun f hf => ?_⟩
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hf
  exact hv i

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.frame_cone_four_list_of_wordMultiplier

/-- **Frame cone at rank four (Khanh Prop. 4.2, `k ≤ 2`)**, reduced to the word multiplier
`WordMultiplierStatement` (Khanh Lemma 4.1, lane 08). -/
theorem frame_cone_four_of_wordMultiplier (h : WordMultiplierStatement)
    (F : Finset (List (Fin 4 → BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))))
    (hF : ∀ f ∈ F, f.length ≤ 2 ∧ IsFrame f) :
    ∃ v, ∀ f ∈ F, IsFrame (v :: f) := by
  obtain ⟨v, hv⟩ := frame_cone_four_list_of_wordMultiplier h F.toList
    (fun f hf => hF f (Finset.mem_toList.mp hf))
  exact ⟨v, fun f hf => hv f (Finset.mem_toList.mpr hf)⟩

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.frame_cone_four_of_wordMultiplier

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone
