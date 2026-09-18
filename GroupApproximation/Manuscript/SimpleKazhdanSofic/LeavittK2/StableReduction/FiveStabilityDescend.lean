import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.StableReduction.FiveStabilityKernel
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.UsedRankFourIntertwine
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVH2GL3.RankFive
import GroupApproximation.Meta.AxiomGuard

/-!
# Descending a stable death one rank, and centrality from one step (sk-leavitt-28, part 3)

Let `R` be a ring with a Leavitt family `L`.

* `fiveStability_refineLast_indexMap`: for `n ≤ M`, refining the last index of `St_{M+1}(R)`
  after padding from rank `n` is padding from rank `n` to rank `M + 2`.  Padded generators never
  touch the last index, so the refinement moves them along `Fin.castSucc` only.
* `fiveStability_descend`: if `K₂(M + 1, R)` is central and `4 ≤ n ≤ M`, an element of `St_n(R)`
  dying in `St_{M+2}(R)` already dies in `St_{M+1}(R)`.  The refinement `D` of the last index is
  injective when `K₂` is central (`fiveStability_eq_one_of_refineHom_eq_one`), and `D ∘ pad = pad`.
* `fiveStability_K2_le_center_of_k2StabInjective`: injective stability at rank `m` makes
  `K₂(m, R)` central.  For `z ∈ K₂(m)` and `g`, the commutator `g z g⁻¹ z⁻¹` lies in `K₂(m)` and
  dies one rank up, because padded `K₂` is central there (Khanh, Lemma 5.2).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open GroupApproximation.SteinbergGroup

variable {R : Type*} [Ring R] (L : LeavittFamily R)

/-- **Refining the last index after padding is padding.**  For `n ≤ M`,
`D_{last M} ∘ pad_{n → M+1} = pad_{n → M+2}`. -/
theorem fiveStability_refineLast_indexMap {n M : ℕ} (h : n ≤ M) :
    (LeavittFP.refineHom L (Fin.last M)).comp
        (indexMap (R := R) (Fin.castLEEmb (show n ≤ M + 1 by omega))) =
      indexMap (R := R) (Fin.castLEEmb (show n ≤ M + 1 + 1 by omega)) := by
  apply PresentedGroup.ext
  rintro ⟨i, j, hij, a⟩
  change LeavittFP.refineHom L (Fin.last M)
      (indexMap (Fin.castLEEmb (show n ≤ M + 1 by omega)) (x i j hij a)) =
    indexMap (Fin.castLEEmb (show n ≤ M + 1 + 1 by omega)) (x i j hij a)
  rw [indexMap_x, indexMap_x, LeavittFP.refineHom_x]
  have hi : ¬ Fin.castLEEmb (show n ≤ M + 1 by omega) i = Fin.last M := fun e => by
    have h1 : i.val = M := congrArg Fin.val e
    have h2 := i.isLt
    omega
  have hj : ¬ Fin.castLEEmb (show n ≤ M + 1 by omega) j = Fin.last M := fun e => by
    have h1 : j.val = M := congrArg Fin.val e
    have h2 := j.isLt
    omega
  rw [LeavittFP.refineRoot_of_plain L (Fin.last M)
    ((Fin.castLEEmb (show n ≤ M + 1 by omega)).injective.ne hij) a hi hj]
  apply usedRankFour_x_congr <;> exact Fin.ext rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStability_refineLast_indexMap

include L in
/-- **Descending one rank.**  If `K₂(M + 1, R)` is central and `4 ≤ n ≤ M`, an element of
`St_n(R)` dying in `St_{M+2}(R)` dies in `St_{M+1}(R)`. -/
theorem fiveStability_descend {n M : ℕ} (hn : 4 ≤ n) (h : n ≤ M)
    (hC : BooneHigman.SteinbergBasic.K2 (Fin (M + 1)) R ≤
      Subgroup.center (SteinbergGroup (Fin (M + 1)) R))
    {w : SteinbergGroup (Fin n) R}
    (hw : indexMap (R := R) (Fin.castLEEmb (show n ≤ M + 1 + 1 by omega)) w = 1) :
    indexMap (R := R) (Fin.castLEEmb (show n ≤ M + 1 by omega)) w = 1 := by
  have hD : LeavittFP.refineHom L (Fin.last M)
      (indexMap (R := R) (Fin.castLEEmb (show n ≤ M + 1 by omega)) w) = 1 :=
    (DFunLike.congr_fun (fiveStability_refineLast_indexMap L h) w).trans hw
  exact fiveStability_eq_one_of_refineHom_eq_one L (by omega) (Fin.last M) ⟨0, by omega⟩
    (fun e => by
      have h1 : (0 : ℕ) = M := congrArg Fin.val e
      omega) hC hD

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStability_descend

/-- **Injective stability at rank `m` makes `K₂(m)` central.**  The commutator of `z ∈ K₂(m)`
with any `g` lies in `K₂(m)` and dies in `St_{m+1}(R)`, since padded `K₂` is central there. -/
theorem fiveStability_K2_le_center_of_k2StabInjective {m : ℕ}
    (hS : Full.LVH2GL3.K2StabInjective R m) :
    BooneHigman.SteinbergBasic.K2 (Fin m) R ≤ Subgroup.center (SteinbergGroup (Fin m) R) := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro g
  have hz' : z ∈ (projection (I := Fin m) (R := R)).ker := hz
  have hc : g * z * g⁻¹ * z⁻¹ ∈ BooneHigman.SteinbergBasic.K2 (Fin m) R :=
    Subgroup.mul_mem _ ((BooneHigman.SteinbergBasic.K2_normal (Fin m) R).conj_mem z hz g)
      (Subgroup.inv_mem _ hz)
  have hcomm : indexMap (R := R) (Fin.castLEEmb (Nat.le_succ m)) g *
        indexMap (R := R) (Fin.castLEEmb (Nat.le_succ m)) z =
      indexMap (R := R) (Fin.castLEEmb (Nat.le_succ m)) z *
        indexMap (R := R) (Fin.castLEEmb (Nat.le_succ m)) g :=
    Subgroup.mem_center_iff.mp (Full.LVCentral.castSuccStab_mem_center hz')
      (indexMap (R := R) (Fin.castLEEmb (Nat.le_succ m)) g)
  have hpc : indexMap (R := R) (Fin.castLEEmb (Nat.le_succ m)) (g * z * g⁻¹ * z⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [hcomm, mul_inv_cancel_right, mul_inv_cancel]
  have hc1 : g * z * g⁻¹ * z⁻¹ = 1 :=
    hS _ ((BooneHigman.SteinbergBasic.mem_K2_iff _).mp hc) hpc
  exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hc1)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStability_K2_le_center_of_k2StabInjective

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
