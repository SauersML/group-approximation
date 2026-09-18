import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnRelK1.Realize
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnK2.Coefficients

/-!
# Relative `K₁` lifting for the Cohn surjection

Let `g ∈ St_n(C₂(𝔽₂))` map into `K₂(n, L_{𝔽₂}(1,2))`.  Pad `g` to rank `N = n + 2` and write
`P ∈ E_N(C₂(𝔽₂))` for its projection.  Then `P ≡ 1` modulo the kernel ideal `(p) ≅ M_∞(𝔽₂)`, so
`P = 1 + ∑ B_{ab} E_{ab}` for an `𝔽₂`-matrix `B` over the corner matrix units.  Over the field `𝔽₂`
the matrix `1 + B` is invertible, with trivial determinant, so it is a product of transvections.
Each transvection is realized by a Steinberg element that dies over the Leavitt algebra, which
gives `cohn_relativeKOneLift`.  This is step W1 of `simple_kazhdan_sofic_group.tex` l.733-735
(Ara-Brustenga-Cortiñas 2009, excision for `(p) ≅ M_∞(𝔽₂)` and `𝔽₂ˣ = 1`).
-/

namespace GroupApproximation.Full.LVCohnRelK1

open SteinbergGroup

noncomputable section

/-- The projection of a Steinberg element in the relative kernel is `1` over the Leavitt algebra
(`simple_kazhdan_sofic_group.tex` l.733-735). -/
theorem mapMatrix_projVal_eq_one {N : ℕ} {g : SteinbergGroup (Fin N) CohnTwoF2}
    (hg : projection (ringMap toLeavitt g) = 1) :
    toLeavitt.mapMatrix (projVal g) = 1 := by
  have h1 := congrArg
    (fun u : elementaryGroup (Fin N) (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) =>
      ((u : (Matrix (Fin N) (Fin N) (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)))ˣ) :
        Matrix (Fin N) (Fin N) (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))))
    ((LVCohnK2.projection_ringMap toLeavitt g).symm.trans hg)
  exact h1

/-- A matrix that is `1` over the Leavitt algebra is `1` modulo the kernel ideal
(`simple_kazhdan_sofic_group.tex` l.733-735). -/
theorem sub_one_mem_cohnIdeal {N : ℕ} {P : Matrix (Fin N) (Fin N) CohnTwoF2}
    (hP : toLeavitt.mapMatrix P = 1) (i j : Fin N) : (P - 1) i j ∈ cohnIdeal := by
  apply mem_cohnIdeal_of_toLeavitt_eq_zero
  have h0 : toLeavitt.mapMatrix (P - 1) = 0 := by
    rw [map_sub, map_one, hP, sub_self]
  have h := congrFun (congrFun h0 i) j
  exact h

/-- **Relative `K₁` lifting for `C₂(𝔽₂) → L_{𝔽₂}(1,2)`**: step W1 of
`simple_kazhdan_sofic_group.tex` l.733-735 (Ara-Brustenga-Cortiñas 2009). -/
theorem cohn_relativeKOneLift : LVStableK2.RelativeKOneLift toLeavitt := by
  intro n g hg
  have h : n ≤ n + 2 := Nat.le_add_right n 2
  refine ⟨n + 2, h, ?_⟩
  have hg1 : projection (ringMap toLeavitt (indexMap (Fin.castLEEmb h) g)) = 1 := by
    rw [← LVStableK2.indexMap_ringMap]
    exact LVH2GL3.projection_indexMap_eq_one (Fin.castLEEmb h) hg
  have hP := mapMatrix_projVal_eq_one hg1
  obtain ⟨W, f, hf⟩ := exists_common_support
    (fun q : Fin (n + 2) × Fin (n + 2) => (projVal (indexMap (Fin.castLEEmb h) g) - 1) q.1 q.2)
    fun q => sub_one_mem_cohnIdeal hP q.1 q.2
  have hsum : unitSum (cornerE W (n + 2)) (Matrix.of fun a b : Fin (n + 2) × W =>
      f (a.1, b.1) a.2 b.2) = projVal (indexMap (Fin.castLEEmb h) g) - 1 :=
    unitSum_cornerE W _ _ fun i j => hf (i, j)
  have hlift : unitLift (cornerE W (n + 2)) (1 + Matrix.of fun a b : Fin (n + 2) × W =>
      f (a.1, b.1) a.2 b.2) = projVal (indexMap (Fin.castLEEmb h) g) := by
    rw [unitLift, add_sub_cancel_left, hsum, add_sub_cancel]
  obtain ⟨u, hu⟩ : ∃ u : (Matrix (Fin (n + 2)) (Fin (n + 2)) CohnTwoF2)ˣ,
      (u : Matrix (Fin (n + 2)) (Fin (n + 2)) CohnTwoF2) =
        projVal (indexMap (Fin.castLEEmb h) g) := ⟨_, rfl⟩
  have hG : ((u⁻¹ : (Matrix (Fin (n + 2)) (Fin (n + 2)) CohnTwoF2)ˣ) :
      Matrix (Fin (n + 2)) (Fin (n + 2)) CohnTwoF2) *
        unitLift (cornerE W (n + 2)) (1 + Matrix.of fun a b : Fin (n + 2) × W =>
          f (a.1, b.1) a.2 b.2) = 1 := by
    rw [hlift, ← hu]
    exact Units.inv_mul u
  have hD : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  obtain ⟨L, hL⟩ := unitLift_factor (cornerE_mul W (n + 2)) hD _ hG
  obtain ⟨t, ht1, ht2⟩ := exists_lift_prod W L
  refine ⟨t, ht1, ?_⟩
  apply Subtype.ext
  apply Units.ext
  exact ht2.trans (hL.symm.trans hlift)

end

end GroupApproximation.Full.LVCohnRelK1
