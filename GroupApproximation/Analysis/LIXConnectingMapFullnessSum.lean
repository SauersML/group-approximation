import GroupApproximation.Analysis.LIXConnectingMapFullness

set_option autoImplicit false

/-!
# A section nonzero in every fibre is full

This module is slow — about 110 seconds, under a four-million heartbeat budget — because
the assembly carries the whole ambient algebra `M_{E_j}(C(X_j))` through a sum indexed by
`EIdx j × EIdx j`.  It is deliberately alone in its own file so that nothing else waits on
it.

The second half of the manuscript's §5 fullness step.  See
`Analysis/LIXConnectingMapFullness.lean` for the first half and for the matrix-unit
averaging `STW59.sum_single_conj` this file consumes.
-/

namespace GroupApproximation
namespace STW59

open scoped Matrix Kronecker ComplexOrder CStarAlgebra

noncomputable section

namespace Gen

variable (n : ℕ)

set_option maxHeartbeats 4000000 in
/-- **A section of `End E_j` that vanishes in no fibre is full in `A_j`.**

`X := aᴴ a` lies in the corner and `Tr X : C(X_j, ℂ)` is nowhere zero, hence invertible;
scaling the left coefficients of the matrix-unit averaging by that inverse expresses the
unit exactly, so no ε is needed. -/
theorem isFull_of_forall_stageEval_ne_zero (j : ℕ) {c : StageAlgebra n j}
    (hc : ∀ w, stageEval n j w c ≠ 0) :
    GroupApproximation.LIX.IsFull c := by
  classical
  have hidem : Eproj n j * Eproj n j = Eproj n j := (isStarProjection_Eproj n j).isIdempotentElem.eq
  have hmem : Eproj n j * toFunctionMatrix (c : SectionAlgebra (baseX n j) (EIdx n j)) * Eproj n j
      = toFunctionMatrix (c : SectionAlgebra (baseX n j) (EIdx n j)) := toFunctionMatrix_mem_corner c
  have hright : toFunctionMatrix (c : SectionAlgebra (baseX n j) (EIdx n j)) * Eproj n j
      = toFunctionMatrix (c : SectionAlgebra (baseX n j) (EIdx n j)) :=
    idem_right_unit hidem hmem
  have hleft : Eproj n j * (toFunctionMatrix (c : SectionAlgebra (baseX n j) (EIdx n j)))ᴴ
      = (toFunctionMatrix (c : SectionAlgebra (baseX n j) (EIdx n j)))ᴴ := by
    have h := congrArg Matrix.conjTranspose hright
    rw [Matrix.conjTranspose_mul,
      conjTranspose_eq_of_isStarProjection (isStarProjection_Eproj n j)] at h
    exact h
  -- the Gram matrix lies in the corner
  have hXmem : Eproj n j * ((toFunctionMatrix (c : SectionAlgebra (baseX n j) (EIdx n j)))ᴴ
        * toFunctionMatrix (c : SectionAlgebra (baseX n j) (EIdx n j))) * Eproj n j
      = (toFunctionMatrix (c : SectionAlgebra (baseX n j) (EIdx n j)))ᴴ
        * toFunctionMatrix (c : SectionAlgebra (baseX n j) (EIdx n j)) := by
    have hre : Eproj n j * ((toFunctionMatrix (c : SectionAlgebra (baseX n j) (EIdx n j)))ᴴ
          * toFunctionMatrix (c : SectionAlgebra (baseX n j) (EIdx n j))) * Eproj n j
        = (Eproj n j * (toFunctionMatrix (c : SectionAlgebra (baseX n j) (EIdx n j)))ᴴ)
          * (toFunctionMatrix (c : SectionAlgebra (baseX n j) (EIdx n j)) * Eproj n j) := by
      simp only [Matrix.mul_assoc]
    rw [hre, hleft, hright]
  -- its trace is nowhere zero
  have htr : ∀ w, (Matrix.trace ((toFunctionMatrix (c : SectionAlgebra (baseX n j) (EIdx n j)))ᴴ
      * toFunctionMatrix (c : SectionAlgebra (baseX n j) (EIdx n j)))) w ≠ 0 := by
    intro w hw
    refine hc w ?_
    have h2 : (matEval w ((toFunctionMatrix (c : SectionAlgebra (baseX n j) (EIdx n j)))ᴴ
        * toFunctionMatrix (c : SectionAlgebra (baseX n j) (EIdx n j)))).trace = 0 := by
      rw [trace_matEval]
      exact hw
    rw [matEval_mul, matEval_conjTranspose] at h2
    exact eq_zero_of_trace_conjTranspose_mul_self h2
  set Mc := toFunctionMatrix (c : SectionAlgebra (baseX n j) (EIdx n j)) with hMcdef
  set tr : C(baseX n j, ℂ) := Matrix.trace (Mcᴴ * Mc) with htrdef
  set tinv : C(baseX n j, ℂ) := ⟨fun w => (tr w)⁻¹, tr.continuous.inv₀ htr⟩ with htinvdef
  have htinv : tinv * tr = 1 := ContinuousMap.ext fun w => inv_mul_cancel₀ (htr w)
  have hleftMc : Eproj n j * Mc = Mc := idem_left_unit hidem hmem
  have hrightMcH : Mcᴴ * Eproj n j = Mcᴴ := by
    have h := congrArg Matrix.conjTranspose hleftMc
    rw [Matrix.conjTranspose_mul,
      conjTranspose_eq_of_isStarProjection (isStarProjection_Eproj n j)] at h
    exact h
  -- the coefficients, at the level of matrices of functions
  set Xco : EIdx n j × EIdx n j → Matrix (EIdx n j) (EIdx n j) C(baseX n j, ℂ) :=
    fun st => (tinv • (Eproj n j * Matrix.single st.1 st.2 1 * Eproj n j)) * Mcᴴ with hXco
  set Yco : EIdx n j × EIdx n j → Matrix (EIdx n j) (EIdx n j) C(baseX n j, ℂ) :=
    fun st => Eproj n j * Matrix.single st.2 st.1 1 * Eproj n j with hYco
  have hsum : (∑ st : EIdx n j × EIdx n j, Xco st * Mc * Yco st) = Eproj n j := by
    have hkey : ∀ st : EIdx n j × EIdx n j, Xco st * Mc * Yco st
        = tinv • ((Eproj n j * Matrix.single st.1 st.2 1 * Eproj n j) * (Mcᴴ * Mc)
            * (Eproj n j * Matrix.single st.2 st.1 1 * Eproj n j)) := by
      intro st
      show ((tinv • (Eproj n j * Matrix.single st.1 st.2 1 * Eproj n j)) * Mcᴴ) * Mc
          * (Eproj n j * Matrix.single st.2 st.1 1 * Eproj n j) = _
      rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul]
      congr 1
      simp only [Matrix.mul_assoc]
    rw [Finset.sum_congr rfl fun st _ => hkey st, ← Finset.smul_sum, Fintype.sum_prod_type,
      sum_single_conj n j (Mcᴴ * Mc) hXmem, smul_smul, htinv, one_smul]
  -- both families lie in the corner
  have hmemY : ∀ st : EIdx n j × EIdx n j, Eproj n j * Yco st * Eproj n j = Yco st := by
    intro st
    show Eproj n j * (Eproj n j * Matrix.single st.2 st.1 1 * Eproj n j) * Eproj n j
      = Eproj n j * Matrix.single st.2 st.1 1 * Eproj n j
    calc Eproj n j * (Eproj n j * Matrix.single st.2 st.1 1 * Eproj n j) * Eproj n j
        = (Eproj n j * Eproj n j) * Matrix.single st.2 st.1 1 * (Eproj n j * Eproj n j) := by
          simp only [Matrix.mul_assoc]
      _ = Eproj n j * Matrix.single st.2 st.1 1 * Eproj n j := by rw [hidem]
  have hmemX : ∀ st : EIdx n j × EIdx n j, Eproj n j * Xco st * Eproj n j = Xco st := by
    intro st
    show Eproj n j * ((tinv • (Eproj n j * Matrix.single st.1 st.2 1 * Eproj n j)) * Mcᴴ) * Eproj n j
      = (tinv • (Eproj n j * Matrix.single st.1 st.2 1 * Eproj n j)) * Mcᴴ
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    calc Eproj n j * ((Eproj n j * Matrix.single st.1 st.2 1 * Eproj n j) * Mcᴴ) * Eproj n j
        = (Eproj n j * Eproj n j) * Matrix.single st.1 st.2 1 * Eproj n j * (Mcᴴ * Eproj n j) := by
          simp only [Matrix.mul_assoc]
      _ = (Eproj n j * Matrix.single st.1 st.2 1 * Eproj n j) * Mcᴴ := by
          rw [hidem, hrightMcH]
  -- transport to the corner and conclude
  have hXmemS : ∀ st : EIdx n j × EIdx n j, ofFunctionMatrix (Xco st) ∈
      cornerAlgebra (stageProj n j) (isStarProjection_stageProj n j) := by
    intro st
    refine mem_stageAlgebra_iff.mpr ?_
    show ofFunctionMatrix (Eproj n j) * ofFunctionMatrix (Xco st) * ofFunctionMatrix (Eproj n j)
      = ofFunctionMatrix (Xco st)
    rw [← ofFunctionMatrix_mul, ← ofFunctionMatrix_mul, hmemX st]
  have hYmemS : ∀ st : EIdx n j × EIdx n j, ofFunctionMatrix (Yco st) ∈
      cornerAlgebra (stageProj n j) (isStarProjection_stageProj n j) := by
    intro st
    refine mem_stageAlgebra_iff.mpr ?_
    show ofFunctionMatrix (Eproj n j) * ofFunctionMatrix (Yco st) * ofFunctionMatrix (Eproj n j)
      = ofFunctionMatrix (Yco st)
    rw [← ofFunctionMatrix_mul, ← ofFunctionMatrix_mul, hmemY st]
  refine LIX.isFull_of_sum_eq_one
    (x := fun k => ⟨ofFunctionMatrix (Xco ((Fintype.equivFin (EIdx n j × EIdx n j)).symm k)),
      hXmemS _⟩)
    (y := fun k => ⟨ofFunctionMatrix (Yco ((Fintype.equivFin (EIdx n j × EIdx n j)).symm k)),
      hYmemS _⟩) ?_
  refine corner_ext ?_
  rw [coe_stageAlgebra_one, coe_corner_sum]
  have hterm : ∀ k : Fin (Fintype.card (EIdx n j × EIdx n j)),
      (((⟨ofFunctionMatrix (Xco ((Fintype.equivFin (EIdx n j × EIdx n j)).symm k)), hXmemS _⟩ *
        c * ⟨ofFunctionMatrix (Yco ((Fintype.equivFin (EIdx n j × EIdx n j)).symm k)),
          hYmemS _⟩ : StageAlgebra n j)) : SectionAlgebra (baseX n j) (EIdx n j))
      = ofFunctionMatrix (Xco ((Fintype.equivFin (EIdx n j × EIdx n j)).symm k) * Mc
          * Yco ((Fintype.equivFin (EIdx n j × EIdx n j)).symm k)) := by
    intro k
    show ofFunctionMatrix (Xco ((Fintype.equivFin (EIdx n j × EIdx n j)).symm k))
        * (c : SectionAlgebra (baseX n j) (EIdx n j))
        * ofFunctionMatrix (Yco ((Fintype.equivFin (EIdx n j × EIdx n j)).symm k))
      = ofFunctionMatrix (Xco ((Fintype.equivFin (EIdx n j × EIdx n j)).symm k) * Mc
          * Yco ((Fintype.equivFin (EIdx n j × EIdx n j)).symm k))
    rw [ofFunctionMatrix_mul (Xco ((Fintype.equivFin (EIdx n j × EIdx n j)).symm k) * Mc)
        (Yco ((Fintype.equivFin (EIdx n j × EIdx n j)).symm k)),
      ofFunctionMatrix_mul (Xco ((Fintype.equivFin (EIdx n j × EIdx n j)).symm k)) Mc,
      hMcdef, ofFunctionMatrix_toFunctionMatrix]
  rw [Finset.sum_congr rfl fun k _ => hterm k, ← ofFunctionMatrix_sum,
    Fintype.sum_equiv (Fintype.equivFin (EIdx n j × EIdx n j)).symm _
      (fun st => Xco st * Mc * Yco st) (fun _ => rfl), hsum]
  rfl

/-- **The stage-level fullness input the simplicity argument consumes.**  If `b ∈ A_i` does
not vanish at the stage point `x_i`, then `φ_i(b)` is full in `A_{i+1}`. -/
theorem isFull_connect_of_stageEval_ne_zero (i : ℕ) {b : StageAlgebra n i}
    (hb : stageEval n i (stagePoint n i) b ≠ 0) :
    GroupApproximation.LIX.IsFull (connect n i b) :=
  isFull_of_forall_stageEval_ne_zero n (i + 1) (stageEval_connect_ne_zero n i hb)


end Gen

/-! ### The `n = 2` instance -/

/-- **A section of `End E_j` that vanishes in no fibre is full in `A_j`.** -/
theorem isFull_of_forall_stageEval_ne_zero (j : ℕ) {c : StageAlgebra j}
    (hc : ∀ w, stageEval j w c ≠ 0) : GroupApproximation.LIX.IsFull c :=
  Gen.isFull_of_forall_stageEval_ne_zero 2 j hc

/-- **The stage-level fullness input the simplicity argument consumes.**  If `b ∈ A_i` does
not vanish at the stage point `x_i`, then `φ_i(b)` is full in `A_{i+1}`. -/
theorem isFull_connect_of_stageEval_ne_zero (i : ℕ) {b : StageAlgebra i}
    (hb : stageEval i (stagePoint i) b ≠ 0) :
    GroupApproximation.LIX.IsFull (connect i b) :=
  Gen.isFull_connect_of_stageEval_ne_zero 2 i hb

end

end STW59
end GroupApproximation
