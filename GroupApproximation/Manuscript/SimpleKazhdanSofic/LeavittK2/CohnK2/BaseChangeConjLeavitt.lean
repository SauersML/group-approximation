import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnK2.BaseChangeConjRelative
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnK2.BaseChangeProof
import GroupApproximation.Leavitt.UniversalLeavittOver
import GroupApproximation.Meta.AxiomGuard

/-!
# Isolated gap: the conjugation form of base change over `L_{𝔽₂}(1,2)`

Lane `sk-leavitt-27`, second module.  Write `C = C_2(𝔽₂)`, `L = L_{𝔽₂}(1,2)`,
`π = toLeavitt : C → L`, `ι = algebraMap 𝔽₂ C` and `ι_L = algebraMap 𝔽₂ L`.

**Truth check.**  `CohnBaseChangeConjStatement` is true (stable `K₂(C) = 0` by
Ara–Brustenga–Cortiñas; take `y = 1`, `g = 1`).  It is not closed here.  The relative
`(p)`-route is circular (`BaseChangeConjRelative.lean`).

**What the target carries that is not needed.**  `BinaryCohnStableK2TrivialStatement` is used
only to reach `BinaryLeavittStableK2TrivialStatement`.  Modulo stable `K₂(𝔽₂) = 0`, the target
is the conjunction of two parts:
* the Leavitt endpoint;
* relative excision `K₂(C, (p)) ≅ K₂(𝔽₂)`.

The second part is never used downstream.

**Isolated gap.**  `LeavittBaseChangeConjStatement`: every `k ∈ K₂(n, L)` is, after padding,
conjugate in `St_N(L)` to `ι_L y` for some `y ∈ St_N(𝔽₂)`.
* *Strictly smaller.*  The target implies it (`leavittBaseChangeConj_of_cohnConj`: lift `k` to
  `K₂(C)` and push the conjugation through `π`).  The Leavitt endpoint implies it with `y = 1`
  (`leavittConj_of_leavittK2`).  The converse of the first implication is excision, which is
  not available.
* *Sufficient.*  With stable `K₂(𝔽₂) = 0` (lane `sk-leavitt-23`) it gives the Leavitt endpoint
  (`leavittK2_of_leavittConj`).  The argument is the one of `cohnBaseChange_of_conj`, run over
  `L` (`L ≠ 0`):
  1. absorb `g` by padding once, using centrality;
  2. get `y ∈ K₂` from injectivity of `E_N(𝔽₂) → E_N(L)`;
  3. kill `y` with stable `K₂(𝔽₂) = 0`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic

/-- **Isolated gap (lane `sk-leavitt-27`).**  After stabilisation, every
`k ∈ K₂(n, L_{𝔽₂}(1,2))` is conjugate in `St_N(L)` to the image of a Steinberg element over
`𝔽₂`.  True: stable `K₂(L_{𝔽₂}(1,2)) = 0`, so `y = 1`, `g = 1` work. -/
def LeavittBaseChangeConjStatement : Prop :=
  ∀ (n : ℕ)
    (k : GroupApproximation.SteinbergGroup (Fin n)
      (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))),
    k ∈ GroupApproximation.BooneHigman.SteinbergBasic.K2 (Fin n)
      (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) →
    ∃ (N : ℕ) (h : n ≤ N) (y : GroupApproximation.SteinbergGroup (Fin N) (ZMod 2))
      (g : GroupApproximation.SteinbergGroup (Fin N)
        (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))),
      GroupApproximation.SteinbergGroup.ringMap
          (algebraMap (ZMod 2) (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))) y =
        g * GroupApproximation.SteinbergGroup.indexMap (Fin.castLEEmb h) k * g⁻¹

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.LeavittBaseChangeConjStatement

/-- The Cohn conjugation form implies the Leavitt conjugation form. -/
theorem leavittBaseChangeConj_of_cohnConj (hC : CohnBaseChangeConjStatement) :
    LeavittBaseChangeConjStatement := by
  intro n k hk
  obtain ⟨k', hk', hk'k⟩ := CohnTwo.exists_K2_lift_of_leavittK2 hk
  obtain ⟨N, hN, y, g, hy⟩ := hC (n + 2) k' hk'
  have hcomp : (CohnTwo.toLeavitt (ZMod 2)).toRingHom.comp
      (algebraMap (ZMod 2) (CohnTwo (ZMod 2))) =
      algebraMap (ZMod 2) (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) :=
    RingHom.ext fun a => (CohnTwo.toLeavitt (ZMod 2)).commutes a
  have h := congrArg (ringMap (I := Fin N) (CohnTwo.toLeavitt (ZMod 2)).toRingHom) hy
  rw [GroupApproximation.BooneHigman.SteinbergBasic.ringMap_ringMap, hcomp, map_mul, map_mul,
    map_inv, ← CohnTwo.indexMap_castLE_ringMap, hk'k, CohnTwo.indexMap_castLE_castLE] at h
  exact ⟨N, (Nat.le_add_right n 2).trans hN, y,
    ringMap (CohnTwo.toLeavitt (ZMod 2)).toRingHom g, h⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.leavittBaseChangeConj_of_cohnConj

/-- **Reduction.**  The Leavitt conjugation form and stable `K₂(𝔽₂) = 0` give stable
`K₂(L_{𝔽₂}(1,2)) = 0`. -/
theorem leavittK2_of_leavittConj (hC : LeavittBaseChangeConjStatement)
    (hF : FieldTwoStableK2Statement) : BinaryLeavittStableK2TrivialStatement := by
  intro n k hk
  obtain ⟨N, hN, y, g, hy⟩ := hC n k hk
  have hinj : Function.Injective
      (algebraMap (ZMod 2) (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))) :=
    RingHom.injective _
  have hc : indexMap (Fin.castLEEmb (Nat.le_add_right N 1)) (indexMap (Fin.castLEEmb hN) k) ∈
      Subgroup.center
        (St (N + 1) (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))) :=
    map_stab_K2_le_center (R := GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))
      (n := N) (Subgroup.mem_map_of_mem
        (stab N (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)))
        (indexMap_mem_K2 (Fin.castLEEmb hN) hk))
  have hc' := Subgroup.mem_center_iff.mp hc
    (indexMap (Fin.castLEEmb (Nat.le_add_right N 1)) g)
  have hmain : ringMap
      (algebraMap (ZMod 2) (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)))
      (indexMap (Fin.castLEEmb (Nat.le_add_right N 1)) y) =
      indexMap (Fin.castLEEmb (hN.trans (Nat.le_add_right N 1))) k := by
    rw [← CohnTwo.indexMap_castLE_ringMap
        (algebraMap (ZMod 2) (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)))
        (Nat.le_add_right N 1) y, hy, map_mul, map_mul, map_inv, hc', mul_inv_cancel_right,
      CohnTwo.indexMap_castLE_castLE hN (Nat.le_add_right N 1) k]
  have hK : projection (ringMap
      (algebraMap (ZMod 2) (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)))
      (indexMap (Fin.castLEEmb (Nat.le_add_right N 1)) y)) = 1 := by
    rw [hmain]
    exact (mem_K2_iff _).mp
      (indexMap_mem_K2 (Fin.castLEEmb (hN.trans (Nat.le_add_right N 1))) hk)
  rw [projection_ringMap] at hK
  have h1 : elementaryGroupMap
      (algebraMap (ZMod 2) (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)))
      (projection (indexMap (Fin.castLEEmb (Nat.le_add_right N 1)) y)) =
      elementaryGroupMap
        (algebraMap (ZMod 2) (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)))
        1 := by
    rw [hK, map_one]
  have hy2 : indexMap (Fin.castLEEmb (Nat.le_add_right N 1)) y ∈ K2 (Fin (N + 1)) (ZMod 2) := by
    rw [mem_K2_iff]
    exact elementaryGroupMap_injective _ hinj h1
  obtain ⟨M, hM, hMy⟩ := hF (N + 1) _ hy2
  refine ⟨M, (hN.trans (Nat.le_add_right N 1)).trans hM, ?_⟩
  rw [← CohnTwo.indexMap_castLE_castLE (hN.trans (Nat.le_add_right N 1)) hM, ← hmain,
    CohnTwo.indexMap_castLE_ringMap, hMy, map_one]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.leavittK2_of_leavittConj

/-- The Leavitt endpoint implies the Leavitt conjugation form (take `y = 1`, `g = 1`). -/
theorem leavittConj_of_leavittK2 (hL : BinaryLeavittStableK2TrivialStatement) :
    LeavittBaseChangeConjStatement := by
  intro n k hk
  obtain ⟨N, hN, hNk⟩ := hL n k hk
  exact ⟨N, hN, 1, 1, by rw [hNk, map_one, one_mul, inv_one, mul_one]⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.leavittConj_of_leavittK2

/-- Modulo stable `K₂(𝔽₂) = 0`, the isolated gap is exactly the Leavitt endpoint. -/
theorem leavittConj_iff_leavittK2 (hF : FieldTwoStableK2Statement) :
    LeavittBaseChangeConjStatement ↔ BinaryLeavittStableK2TrivialStatement :=
  ⟨fun hC => leavittK2_of_leavittConj hC hF, leavittConj_of_leavittK2⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.leavittConj_iff_leavittK2

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
