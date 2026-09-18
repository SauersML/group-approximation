import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnK2.BaseChange
import GroupApproximation.Meta.AxiomGuard

/-!
# The relative `(p)`-step for `C_2(𝔽₂)` is equivalent to stable `K₂(L) = 0`

Lane `sk-leavitt-27`, first module.  Write `C = C_2(𝔽₂)`, `L = L_{𝔽₂}(1,2)`,
`π = toLeavitt : C → L` and `I = (p) = ker π`.

**Circularity (loud).**  The obvious relative route to `CohnBaseChangeConjStatement` splits
`K₂(C)` along `π` into two steps:
1. every `k ∈ K₂(n, C)` pads into `ker (St_N(C) → St_N(L))`
   (`CohnRelativeK2SurjectiveStatement`, the relative surjectivity step);
2. every element of `K₂(N, C) ∩ ker π` is, after padding, conjugate to an `𝔽₂`-image
   (relative triviality: excision, `K₂(C, I) ≅ K₂(𝔽₂)`).

This module proves that step 1 is **equivalent** to `BinaryLeavittStableK2TrivialStatement`,
which is the downstream endpoint that the base-change statements exist to feed
(`cohnRelativeK2Surjective_iff_leavittK2`).  So the relative route is not a smaller gap.
* `⇐`: `π k ∈ K₂(n, L)` pads to `1`, and padding commutes with `π`.
* `⇒`: pad `k ∈ K₂(n, L)` to rank `n + 2` and lift it to `k' ∈ K₂(n + 2, C)`
  (`CohnTwo.exists_K2_lift_of_leavittK2`, using the proved relative `K₁(C, I) = 0`).  Step 1
  puts `k'` in `ker π` after padding, so the padded `k` is `1`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic

/-- **Relative surjectivity step.**  Every `k ∈ K₂(n, C_2(𝔽₂))` pads to an element of
`ker (St_N(C_2) → St_N(L))`.  True: stable `K₂(C_2(𝔽₂)) = 0`.  Equivalent to
`BinaryLeavittStableK2TrivialStatement` (`cohnRelativeK2Surjective_iff_leavittK2`). -/
def CohnRelativeK2SurjectiveStatement : Prop :=
  ∀ (n : ℕ) (k : GroupApproximation.SteinbergGroup (Fin n) (CohnTwo (ZMod 2))),
    k ∈ GroupApproximation.BooneHigman.SteinbergBasic.K2 (Fin n) (CohnTwo (ZMod 2)) →
    ∃ (N : ℕ) (h : n ≤ N),
      GroupApproximation.SteinbergGroup.ringMap (CohnTwo.toLeavitt (ZMod 2)).toRingHom
        (GroupApproximation.SteinbergGroup.indexMap (Fin.castLEEmb h) k) = 1

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK2SurjectiveStatement

namespace CohnTwo

/-- Padded `K₂(L)` lifts to `K₂(C_2)`: every `k ∈ K₂(n, L)`, padded to rank `n + 2`, is the
image under `π` of some `k' ∈ K₂(n + 2, C_2)`.  Uses the proved relative `K₁(C_2, (p)) = 0`. -/
theorem exists_K2_lift_of_leavittK2 {n : ℕ}
    {k : GroupApproximation.SteinbergGroup (Fin n)
      (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))}
    (hk : k ∈ K2 (Fin n) (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))) :
    ∃ k' : GroupApproximation.SteinbergGroup (Fin (n + 2)) (CohnTwo (ZMod 2)),
      k' ∈ K2 (Fin (n + 2)) (CohnTwo (ZMod 2)) ∧
        ringMap (toLeavitt (ZMod 2)).toRingHom k' =
          indexMap (Fin.castLEEmb (Nat.le_add_right n 2)) k := by
  have hk2 := indexMap_mem_K2 (Fin.castLEEmb (Nat.le_add_right n 2)) hk
  obtain ⟨x, hx⟩ := ringMap_surjective_of_surjective (I := Fin (n + 2))
    (toLeavitt (ZMod 2)).toRingHom (toLeavitt_surjective (ZMod 2))
    (indexMap (Fin.castLEEmb (Nat.le_add_right n 2)) k)
  rw [← hx] at hk2
  obtain ⟨t, ht1, htx⟩ :=
    projection_lift_of_relativeKOne cohnRelativeKOneTrivial (Nat.le_add_left 2 n) x hk2
  refine ⟨x * t⁻¹, ?_, ?_⟩
  · rw [mem_K2_iff, map_mul, map_inv, htx, mul_inv_cancel]
  · rw [map_mul, map_inv, ht1, inv_one, mul_one]
    exact hx

end CohnTwo

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.exists_K2_lift_of_leavittK2

/-- The relative surjectivity step gives stable `K₂(L) = 0`. -/
theorem leavittK2_of_cohnRelativeK2Surjective (hG : CohnRelativeK2SurjectiveStatement) :
    BinaryLeavittStableK2TrivialStatement := by
  intro n k hk
  obtain ⟨k', hk', hk'k⟩ := CohnTwo.exists_K2_lift_of_leavittK2 hk
  obtain ⟨N, hN, hNk⟩ := hG (n + 2) k' hk'
  refine ⟨N, (Nat.le_add_right n 2).trans hN, ?_⟩
  rw [← CohnTwo.indexMap_castLE_castLE (Nat.le_add_right n 2) hN, ← hk'k,
    CohnTwo.indexMap_castLE_ringMap, hNk]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.leavittK2_of_cohnRelativeK2Surjective

/-- Stable `K₂(L) = 0` gives the relative surjectivity step. -/
theorem cohnRelativeK2Surjective_of_leavittK2 (hL : BinaryLeavittStableK2TrivialStatement) :
    CohnRelativeK2SurjectiveStatement := by
  intro n k hk
  obtain ⟨N, hN, hNk⟩ := hL n (ringMap (CohnTwo.toLeavitt (ZMod 2)).toRingHom k)
    (ringMap_mem_K2 _ hk)
  refine ⟨N, hN, ?_⟩
  rw [← CohnTwo.indexMap_castLE_ringMap, hNk]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.cohnRelativeK2Surjective_of_leavittK2

/-- **Loud circularity.**  The relative `(p)`-surjectivity step for `C_2(𝔽₂)` is equivalent to
stable `K₂(L_{𝔽₂}(1,2)) = 0`. -/
theorem cohnRelativeK2Surjective_iff_leavittK2 :
    CohnRelativeK2SurjectiveStatement ↔ BinaryLeavittStableK2TrivialStatement :=
  ⟨leavittK2_of_cohnRelativeK2Surjective, cohnRelativeK2Surjective_of_leavittK2⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.cohnRelativeK2Surjective_iff_leavittK2

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
