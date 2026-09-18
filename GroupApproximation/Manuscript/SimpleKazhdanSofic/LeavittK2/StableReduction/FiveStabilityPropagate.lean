import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.StableReduction.FiveStabilityKernel
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.UsedRankFourIntertwine
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.StableReduction.StableKTwo
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVH2GL3.RankFive
import GroupApproximation.Leavitt.UniversalLeavittOver
import GroupApproximation.Meta.AxiomGuard

/-!
# Stability from rank five climbs, and equals rank-by-rank injectivity (sk-leavitt-28, part 2)

Write `L = L_{𝔽₂}(1,2)`.  `fiveStability_propagate` shows, for any ring with a Leavitt family and
`n ≥ 4` with a spare index, that stable injectivity at rank `n` gives stable injectivity at rank
`n + 1`.  Take `z = D w ∈ K₂(n + 1)` with `D = LeavittFP.refineHom L r`, dying in
`St_{N+1}(R)`.

* The intertwining identity (`usedRankFour_intertwine`) and injectivity of the index swap give
  `D' (pad w) = 1` at rank `N`, where `D'` refines `castLE r`.
* Padding kills `ker D'` (`fiveStability_indexMap_eq_one_of_refineHom_eq_one`), so `w` dies in
  `St_{N+1}(R)`.  The hypothesis at rank `n` gives `w = 1`, hence `z = 1`.

## Consequence

`BinaryLeavittK2FiveStabilityStatement` is **equivalent** to
`∀ m ≥ 5, Full.LVH2GL3.K2StabInjective L m`, and both directions are proved here.  The rank-by-rank
family is therefore *not* a smaller statement than the target; it is a restatement.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open GroupApproximation.SteinbergGroup

variable {R : Type*} [Ring R] (L : LeavittFamily R)

/-- Padding along the index swap is injective: the inverse swap undoes it. -/
theorem fiveStability_indexMap_swap_injective {n N : ℕ} (h : n ≤ N) :
    Function.Injective (indexMap (R := R) (usedRankFourSwap h).toEmbedding) := by
  have hinv : (indexMap (R := R) (usedRankFourSwap h).symm.toEmbedding).comp
      (indexMap (R := R) (usedRankFourSwap h).toEmbedding) =
        MonoidHom.id (SteinbergGroup (Fin (N + 1)) R) := by
    apply PresentedGroup.ext
    rintro ⟨i, j, hij, a⟩
    change indexMap (usedRankFourSwap h).symm.toEmbedding
        (indexMap (usedRankFourSwap h).toEmbedding (x i j hij a)) = x i j hij a
    rw [indexMap_x, indexMap_x]
    exact usedRankFour_x_congr ((usedRankFourSwap h).symm_apply_apply i)
      ((usedRankFourSwap h).symm_apply_apply j)
  intro a b hab
  have ha : indexMap (R := R) (usedRankFourSwap h).symm.toEmbedding
      (indexMap (R := R) (usedRankFourSwap h).toEmbedding a) = a := DFunLike.congr_fun hinv a
  have hb : indexMap (R := R) (usedRankFourSwap h).symm.toEmbedding
      (indexMap (R := R) (usedRankFourSwap h).toEmbedding b) = b := DFunLike.congr_fun hinv b
  exact ha.symm.trans
    ((congrArg (indexMap (R := R) (usedRankFourSwap h).symm.toEmbedding) hab).trans hb)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStability_indexMap_swap_injective

/-- **Stable injectivity climbs one rank.**  For `n ≥ 4` with a spare index `k ≠ r`, if every
`K₂(n)` element dying in some `St_N(R)` is trivial, the same holds at rank `n + 1`. -/
theorem fiveStability_propagate {n : ℕ} (hn : 4 ≤ n) (r k : Fin n) (hk : k ≠ r)
    (hT : ∀ w ∈ BooneHigman.SteinbergBasic.K2 (Fin n) R, ∀ (N : ℕ) (h : n ≤ N),
      indexMap (R := R) (Fin.castLEEmb h) w = 1 → w = 1) :
    ∀ z ∈ BooneHigman.SteinbergBasic.K2 (Fin (n + 1)) R, ∀ (M : ℕ) (h : n + 1 ≤ M),
      indexMap (R := R) (Fin.castLEEmb h) z = 1 → z = 1 := by
  intro z hz M hM hzM
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp ((LeavittFP.K2_map_refineHom L r k hk).ge hz)
  obtain ⟨N, rfl⟩ : ∃ N, M = N + 1 := ⟨M - 1, by omega⟩
  have h : n ≤ N := by omega
  have e := DFunLike.congr_fun (usedRankFour_intertwine L r h) w
  simp only [MonoidHom.comp_apply] at e
  have hσ : indexMap (R := R) (usedRankFourSwap h).toEmbedding
      (LeavittFP.refineHom L (Fin.castLE h r) (indexMap (R := R) (Fin.castLEEmb h) w)) = 1 :=
    e.symm.trans hzM
  have hy : LeavittFP.refineHom L (Fin.castLE h r) (indexMap (R := R) (Fin.castLEEmb h) w) = 1 :=
    fiveStability_indexMap_swap_injective h
      (hσ.trans (map_one (indexMap (R := R) (usedRankFourSwap h).toEmbedding)).symm)
  have hk' : Fin.castLE h k ≠ Fin.castLE h r := fun e => hk (Fin.ext (congrArg Fin.val e))
  have hpad := fiveStability_indexMap_eq_one_of_refineHom_eq_one L (by omega)
    (Fin.castLE h r) (Fin.castLE h k) hk' hy
  have hw1 : w = 1 := hT w hw (N + 1) (h.trans (Nat.le_succ N))
    ((Full.LVH2GL3.indexMap_castLEEmb_castLEEmb h (Nat.le_succ N) w).symm.trans hpad)
  rw [hw1, map_one]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStability_propagate

/-- **Stability from rank five holds from every rank `m ≥ 5`** over `L_{𝔽₂}(1,2)`. -/
theorem binaryLeavittK2FiveStability_propagate (hT : BinaryLeavittK2FiveStabilityStatement) :
    ∀ m : ℕ, 5 ≤ m →
      ∀ z ∈ BooneHigman.SteinbergBasic.K2 (Fin m) (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)),
        ∀ (M : ℕ) (h : m ≤ M),
          indexMap (R := BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) (Fin.castLEEmb h) z = 1 →
            z = 1 := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact hT
  | succ m hm ih =>
    exact fiveStability_propagate (BinaryLeavitt.family (ZMod 2)) (by omega)
      (⟨0, by omega⟩ : Fin m) ⟨1, by omega⟩
      (fun e => by
        have h1 : (1 : ℕ) = 0 := congrArg Fin.val e
        omega) ih

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.binaryLeavittK2FiveStability_propagate

/-- The target gives injective stability at every rank `m ≥ 5`. -/
theorem k2StabInjective_of_binaryLeavittK2FiveStability
    (hT : BinaryLeavittK2FiveStabilityStatement) :
    ∀ m : ℕ, 5 ≤ m →
      Full.LVH2GL3.K2StabInjective (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) m := by
  intro m hm k hk hpad
  exact binaryLeavittK2FiveStability_propagate hT m hm k
    ((BooneHigman.SteinbergBasic.mem_K2_iff k).mpr hk) (m + 1) (Nat.le_succ m) hpad

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.k2StabInjective_of_binaryLeavittK2FiveStability

/-- Injective stability at every rank `m ≥ 5` gives the target (telescoping). -/
theorem binaryLeavittK2FiveStability_of_k2StabInjective
    (hT : ∀ m : ℕ, 5 ≤ m →
      Full.LVH2GL3.K2StabInjective (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) m) :
    BinaryLeavittK2FiveStabilityStatement := by
  intro k hk N h hN
  exact Full.LVH2GL3.eq_one_of_indexMap_eq_one hT
    ((BooneHigman.SteinbergBasic.mem_K2_iff k).mp hk) N h hN

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.binaryLeavittK2FiveStability_of_k2StabInjective

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
