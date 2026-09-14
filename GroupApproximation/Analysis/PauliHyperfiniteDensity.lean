import GroupApproximation.Analysis.PauliMatrixUnits

/-!
# The hyperfinite II₁ factor is approximately finite

Infrastructure of lane `oa-hyperfinite` for "Brown's formulation" of `simple_kazhdan_sofic_group.tex`
(tex l.273–290 at 37551fd93), where `𝓡` is the *hyperfinite* II₁ factor.  The Pauli model is
approximately finite in Murray and von Neumann's sense: every element of `𝓡` is approximated in the
2-norm `‖T‖₂ = ‖T δ₁‖` by an element of some finite Pauli stage `stageHom j (M_{2^j}(ℂ))`.

* `pauliMatrix x z`, the signed permutation matrix with `stageOp x z = stageHom j (pauliMatrix x z)`
  (`stageOp_eq_stageHom`), by character orthogonality.
* `exists_stageEmb_eq`: a sequence supported below `j` is a word of length `j`.
* `exists_stageOp_eq`: each twisted left unitary lies in every stage past its support.
* `hyperfiniteFactor_approximatelyFinite`: for `T ∈ 𝓡` and `ε > 0` there are `j` and `A` with
  `‖(T − stageHom j A) δ₁‖ < ε`.  Truncate `ξ = T δ₁` to a finite set `F` with
  `‖ξ − Σ_{g ∈ F} ξ(g) δ_g‖ < ε`, and take `A = Σ_{g ∈ F} ξ(g) · pauliMatrix g`.
-/

namespace GroupApproximation
namespace Hyperfinite

open TwistedGroupVonNeumann ReducedGroupCStarTrace MatrixUnits Filter
open scoped InnerProductSpace

noncomputable section

variable {j : ℕ}

/-- The signed permutation matrix of the stage Pauli operator `stageOp x z`. -/
def pauliMatrix (x z : StageIdx j) : Matrix (StageIdx j) (StageIdx j) ℂ :=
  fun a b ↦ if a = b + x then zsign (fdot z b) else 0

/-- **Each stage Pauli operator lies in the stage.** -/
theorem stageOp_eq_stageHom (x z : StageIdx j) : stageOp x z = stageHom j (pauliMatrix x z) := by
  rw [stageHom, matrixUnitHom_apply]
  have h1 : ∑ a : StageIdx j, ∑ b : StageIdx j, pauliMatrix x z a b • stageUnit a b =
      ∑ b : StageIdx j, zsign (fdot z b) • stageUnit (b + x) b := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    simp only [pauliMatrix, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [h1]
  have h2 : ∀ b : StageIdx j, zsign (fdot z b) • stageUnit (b + x) b =
      ((2 : ℂ) ^ j)⁻¹ • ∑ w : StageIdx j, zsign (fdot (z + w) b) • stageOp x w := by
    intro b
    rw [stageUnit, smul_comm, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    have hidx : b + x + b = x := by
      rw [add_comm b x, add_assoc, stageIdx_add_self, add_zero]
    rw [hidx, smul_smul, ← zsign_add, ← fdot_add_left]
  rw [Finset.sum_congr rfl fun b _ ↦ h2 b, ← Finset.smul_sum, Finset.sum_comm]
  have h3 : ∀ w : StageIdx j, ∑ b : StageIdx j, zsign (fdot (z + w) b) • stageOp x w =
      if w = z then (2 : ℂ) ^ j • stageOp x w else 0 := by
    intro w
    rw [← Finset.sum_smul]
    have hs : ∑ b : StageIdx j, zsign (fdot (z + w) b) =
        if z + w = 0 then (2 : ℂ) ^ j else 0 := by
      rw [← sum_zsign_fdot (z + w)]
      exact Finset.sum_congr rfl fun b _ ↦ by rw [fdot_comm]
    rw [hs]
    have hzw : z + w = 0 ↔ w = z := by
      constructor
      · intro h
        have h' := congrArg (· + z) h
        simpa [add_comm z w, add_assoc, stageIdx_add_self] using h'
      · intro h
        rw [h, stageIdx_add_self]
    by_cases hw : w = z
    · rw [if_pos (hzw.mpr hw), if_pos hw]
    · rw [if_neg (fun h ↦ hw (hzw.mp h)), if_neg hw, zero_smul]
  rw [Finset.sum_congr rfl fun w _ ↦ h3 w]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [smul_smul, inv_mul_cancel₀ (pow_ne_zero j two_ne_zero), one_smul]

/-- A sequence supported below `j` is the embedding of a word of length `j`. -/
theorem exists_stageEmb_eq {v : PauliCoord} (hv : ∀ i ∈ v.support, i < j) :
    ∃ u : StageIdx j, stageEmb u = v := by
  refine ⟨fun i ↦ v i.val, ?_⟩
  ext n
  rw [stageEmb_apply]
  by_cases hn : n < j
  · rw [dif_pos hn]
  · rw [dif_neg hn]
    by_contra h
    exact hn (hv n (Finsupp.mem_support_iff.mpr (Ne.symm h)))

/-- Each twisted left unitary lies in every stage past its support. -/
theorem exists_stageOp_eq (g : PauliGroup)
    (hj : ∀ i ∈ (Multiplicative.toAdd g).1.support ∪ (Multiplicative.toAdd g).2.support, i < j) :
    ∃ x z : StageIdx j, twistedLeftOperator pauliCocycle g = stageOp x z := by
  obtain ⟨x, hx⟩ := exists_stageEmb_eq (j := j) fun i hi ↦ hj i (Finset.mem_union_left _ hi)
  obtain ⟨z, hz⟩ := exists_stageEmb_eq (j := j) fun i hi ↦ hj i (Finset.mem_union_right _ hi)
  refine ⟨x, z, ?_⟩
  simp [stageOp, pauliOp, hx, hz]

/-- **The hyperfinite II₁ factor is approximately finite**: every element is a 2-norm limit of
elements of the finite Pauli stages. -/
theorem hyperfiniteFactor_approximatelyFinite
    {T : GroupHilbert PauliGroup →L[ℂ] GroupHilbert PauliGroup} (_hT : T ∈ hyperfiniteFactor)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ j : ℕ, ∃ A : Matrix (StageIdx j) (StageIdx j) ℂ,
      ‖(T - stageHom j A) (deltaOne PauliGroup)‖ < ε := by
  set ξ := T (deltaOne PauliGroup) with hξ
  have hs : HasSum (fun g : PauliGroup ↦ (lp.single 2 g (ξ g) : GroupHilbert PauliGroup)) ξ :=
    lp.hasSum_single ENNReal.ofNat_ne_top ξ
  obtain ⟨F, hF⟩ := Filter.eventually_atTop.mp (Metric.tendsto_nhds.mp hs ε hε)
  set J := (F.biUnion fun g ↦ (Multiplicative.toAdd g).1.support ∪
    (Multiplicative.toAdd g).2.support).sup id + 1 with hJ
  have hbound : ∀ g ∈ F,
      ∀ i ∈ (Multiplicative.toAdd g).1.support ∪ (Multiplicative.toAdd g).2.support, i < J := by
    intro g hg i hi
    have hle : i ≤ (F.biUnion fun g ↦ (Multiplicative.toAdd g).1.support ∪
        (Multiplicative.toAdd g).2.support).sup id :=
      Finset.le_sup (f := id) (Finset.mem_biUnion.mpr ⟨g, hg, hi⟩)
    omega
  have hex : ∀ g ∈ F, ∃ x z : StageIdx J, twistedLeftOperator pauliCocycle g = stageOp x z :=
    fun g hg ↦ exists_stageOp_eq g (hbound g hg)
  choose! xg zg hxz using hex
  refine ⟨J, ∑ g ∈ F, ξ g • pauliMatrix (xg g) (zg g), ?_⟩
  have hS : (stageHom J (∑ g ∈ F, ξ g • pauliMatrix (xg g) (zg g))) (deltaOne PauliGroup) =
      ∑ g ∈ F, (lp.single 2 g (ξ g) : GroupHilbert PauliGroup) := by
    simp only [map_sum, map_smul, sum_apply, smul_apply]
    refine Finset.sum_congr rfl fun g hg ↦ ?_
    rw [← stageOp_eq_stageHom, ← hxz g hg,
      twistedLeftOperator_deltaOne pauliCocycle pauliCocycle_isSignCocycle, ← lp.single_smul,
      smul_eq_mul, mul_one]
  rw [sub_apply, hS, norm_sub_rev, ← dist_eq_norm]
  exact hF F le_rfl

end

#audit_axioms stageOp_eq_stageHom
#audit_axioms hyperfiniteFactor_approximatelyFinite

end Hyperfinite
end GroupApproximation
