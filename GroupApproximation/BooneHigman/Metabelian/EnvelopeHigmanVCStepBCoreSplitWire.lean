import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCStepBCoreSplit
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCStepBReduce
import Mathlib.Tactic.Group
import GroupApproximation.Meta.AxiomGuard

/-!
# Step B core: the normalised residual gives letter-closure and Higman (1) (lane bh-met-93r)

Notation as in `EnvelopeHigmanVCStepBCoreSplit`.

**Proved here, from `HigmanVCStepBCore_SplitStatement` only.**
* `higmanVCStepBCore_full`: the residual extended to an arbitrary antichain `D` (refining `C`,
  strictly deeper) and an arbitrary involution `P ∈ H_D`.  The one-antichain case is proved
  (`higmanVCStepBCore_mem_S_of_oneAC`).  Otherwise `D` is completed at depth
  `M = max (sup |D|) (L + 1)`; the fill words have length `M > L`, so the completion still
  refines `C` and is strictly deeper than `C`, and `H_D ≤ H_{D'}`.
* `higmanVCStepBCore_closed_of_split`: letter-closure of `S`.  This is the proof of
  `higmanVCStepB_closed_of_core`, except that the pushed letter `P = u₂ ℓ u₂⁻¹` is an
  involution (`ℓ² = 1`), so `higmanVCStepBCore_full` applies.
* `higmanVCStepBCore_ker_le_of_split`, `higmanVCStepBCore_allAC_of_split`: endpoints.

**LOUD: Higman (1) is proved here only conditionally**, on `HigmanVCStepBCore_SplitStatement`,
which is EQUIVALENT as a `Prop` to `HigmanVCStepBCoreStatement` (and to Higman (1)); it has a
strictly smaller, normalised instance set (complete `D`, involutive `P`, one-antichain case
excluded).

Truth check (python, `SP/bh-met-93r/split_check.py`, assuming `Q ≅ V_d` and Claim F, both
product orders): d = 2: 200 instances, 400 of 400 products in `E(S)`, 0 refuted.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- The normalised residual, extended to every strictly deeper refinement `D` of a complete
code `C` and every involution `P ∈ H_D`. -/
theorem higmanVCStepBCore_full (hK : HigmanVCStepBCore_SplitStatement) {d : ℕ} (hd : 1 < d)
    {C : Finset (List (Fin d))} (hC : higmanVCTreeNFWitPivot_IsAC C)
    (hCL : ∃ L : ℕ, (∀ c ∈ C, c.length ≤ L) ∧
      ∀ w : List (Fin d), w.length = L → ∃ c ∈ C, c <+: w)
    {D : Finset (List (Fin d))} (hD : higmanVCTreeNFWitPivot_IsAC D)
    (href : ∀ z ∈ D, ∃ c ∈ C, c <+: z)
    (hdeep : ∀ z ∈ D, ∀ c ∈ C, c.length < z.length)
    {h : higmanVCCommon_Q d} (hh : h ∈ higmanVCTreeNFWitPivot_H d C)
    {P : higmanVCCommon_Q d} (hP : P ∈ higmanVCTreeNFWitPivot_H d D) (hP2 : P * P = 1) :
    h * P ∈ higmanVCTreeNFWitPivot_S d := by
  by_cases hone : higmanVCStepBCore_OneAC d h P
  · exact higmanVCStepBCore_mem_S_of_oneAC hone
  obtain ⟨L, hL, hLc⟩ := hCL
  obtain ⟨M, hM1, hM2⟩ : ∃ M : ℕ, (∀ z ∈ D, z.length ≤ M) ∧ L + 1 ≤ M :=
    ⟨max (D.sup List.length) (L + 1),
      fun z hz => (Finset.le_sup (f := List.length) hz).trans (le_max_left _ _),
      le_max_right _ _⟩
  have hD'M : ∀ z ∈ higmanVCPivotY_complete D M, z.length ≤ M := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact hM1 z hz
    · exact (higmanVCPivotY_mem_fill.mp hz).1.le
  have href' : ∀ z ∈ higmanVCPivotY_complete D M, ∃ c ∈ C, c <+: z := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact href z hz
    · have hzM := (higmanVCPivotY_mem_fill.mp hz).1
      obtain ⟨c, hc, hcw⟩ := hLc (z.take L) (List.length_take_of_le (by omega))
      exact ⟨c, hc, hcw.trans (List.take_prefix L z)⟩
  have hdeep' : ∀ z ∈ higmanVCPivotY_complete D M, ∀ c ∈ C, c.length < z.length := by
    intro z hz c hc
    rcases Finset.mem_union.mp hz with hz | hz
    · exact hdeep z hz c hc
    · have hzM := (higmanVCPivotY_mem_fill.mp hz).1
      have hcL := hL c hc
      omega
  exact hK d hd C hC ⟨L, hL, hLc⟩ (higmanVCPivotY_complete D M)
    (higmanVCPivotY_complete_isAC hD hM1) ⟨M, hD'M, higmanVCPivotY_complete_cover D M⟩
    href' hdeep' h hh P (higmanVCPivotY_H_mono (higmanVCPivotY_subset_complete D M) hP) hP2 hone

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCStepBCore_full

/-- The normalised residual gives letter-closure of `S`. -/
theorem higmanVCStepBCore_closed_of_split (hK : HigmanVCStepBCore_SplitStatement) {d : ℕ}
    (hd : 1 < d) : higmanVCStepB_Closed d := by
  intro s hs x y
  by_cases hxy : ¬ x <+: y ∧ ¬ y <+: x
  swap
  · rw [higmanVCCommon_mk_comparable hxy, mul_one]
    exact hs
  obtain ⟨hxy1, hxy2⟩ := hxy
  obtain ⟨u₁, hu₁, C, hC, h, hh, u₂, hu₂, rfl⟩ := higmanVCTreeNFWitPivot_mem_S.mp hs
  obtain ⟨g, rfl⟩ := higmanVCTreeNF_mk_surjective d u₂
  obtain ⟨N, hN⟩ := higmanVCCommon_push hd g
  obtain ⟨L, hL⟩ : ∃ L : ℕ, ∀ c ∈ C, c.length ≤ L :=
    ⟨C.sup List.length, fun c hc => Finset.le_sup (f := List.length) hc⟩
  have hxyAC := higmanVCStepB_pair_isAC hxy1 hxy2
  have hR := higmanVCPivotAC_refine_isAC hxyAC (L + 1 + N)
  have hℓ : higmanVCCommon_mk d (FreeGroup.of (x, y)) ∈
      higmanVCTreeNFWitPivot_H d (higmanVCPivotAC_refine {x, y} (L + 1 + N)) :=
    higmanVCPivotAC_H_le_refine hxyAC (L + 1 + N)
      (higmanVCLeafExp_letter_mem_H (Finset.mem_insert_self x {y})
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self y)))
  obtain ⟨D, hDdef⟩ : ∃ D : Finset (List (Fin d)),
      D = higmanVCPivotAC_push d (L + 1) g (higmanVCPivotAC_refine {x, y} (L + 1 + N)) :=
    ⟨_, rfl⟩
  have hP : higmanVCCommon_mk d g * higmanVCCommon_mk d (FreeGroup.of (x, y)) *
      (higmanVCCommon_mk d g)⁻¹ ∈ higmanVCTreeNFWitPivot_H d D := by
    rw [hDdef]
    exact higmanVCPivotAC_conj_mem (B := L + 1) hd hN hR
      (fun _ hc => higmanVCPivotAC_refine_length hc) hℓ
  have e2 : ∀ a b : higmanVCCommon_Q d, a * b * a⁻¹ * (a * b * a⁻¹) = a * (b * b) * a⁻¹ := by
    intro a b
    group
  have hP2 : higmanVCCommon_mk d g * higmanVCCommon_mk d (FreeGroup.of (x, y)) *
      (higmanVCCommon_mk d g)⁻¹ * (higmanVCCommon_mk d g *
        higmanVCCommon_mk d (FreeGroup.of (x, y)) * (higmanVCCommon_mk d g)⁻¹) = 1 := by
    rw [e2, higmanVCCommon_mk_sq, mul_one, mul_inv_cancel]
  have hD : higmanVCTreeNFWitPivot_IsAC D := by
    rw [hDdef]
    exact higmanVCPivotAC_push_isAC hd g hR
  have hDlen : ∀ z ∈ D, L + 1 ≤ z.length := by
    intro z hz
    rw [hDdef] at hz
    exact higmanVCPivotAC_push_length hd hz
  have hC'L : ∀ c ∈ higmanVCPivotY_complete C L, c.length ≤ L := by
    intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · exact hL c hc
    · exact (higmanVCPivotY_mem_fill.mp hc).1.le
  have href : ∀ z ∈ D, ∃ c ∈ higmanVCPivotY_complete C L, c <+: z := by
    intro z hz
    have hz' := hDlen z hz
    obtain ⟨c, hc, hcw⟩ := higmanVCPivotY_complete_cover C L (z.take L)
      (List.length_take_of_le (by omega))
    exact ⟨c, hc, hcw.trans (List.take_prefix L z)⟩
  have hdeep : ∀ z ∈ D, ∀ c ∈ higmanVCPivotY_complete C L, c.length < z.length := by
    intro z hz c hc
    have h1 := hDlen z hz
    have h2 := hC'L c hc
    omega
  have key := higmanVCStepBCore_full hK hd (higmanVCPivotY_complete_isAC hC hL)
    ⟨L, hC'L, higmanVCPivotY_complete_cover C L⟩ hD href hdeep
    (higmanVCPivotY_H_mono (higmanVCPivotY_subset_complete C L) hh) hP hP2
  have e : ∀ a b c k : higmanVCCommon_Q d, a * b * c * k = a * (b * (c * k * c⁻¹)) * c := by
    intro a b c k
    group
  rw [e]
  exact higmanVCTreeNFWitPivot_S_mul_U (higmanVCPivotAC_U_mul_S hu₁ key) hu₂

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCStepBCore_closed_of_split

/-- The normalised residual gives Higman's kernel inclusion at every arity `d > 1`. -/
theorem higmanVCStepBCore_ker_le_of_split (hK : HigmanVCStepBCore_SplitStatement) {d : ℕ}
    (hd : 1 < d) :
    (higmanVC_evalAll d).ker ≤ Subgroup.normalClosure (higmanVC_rels d fun _ => True) :=
  higmanVCStepB_ker_le_of_closed hd (higmanVCStepBCore_closed_of_split hK hd)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCStepBCore_ker_le_of_split

/-- **Endpoint.**  The normalised residual gives `HigmanVCAllAntichainStatement`. -/
theorem higmanVCStepBCore_allAC_of_split (hK : HigmanVCStepBCore_SplitStatement) :
    HigmanVCAllAntichainStatement :=
  higmanVCStepB_antichain_of_closed fun _ hd => higmanVCStepBCore_closed_of_split hK hd

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCStepBCore_allAC_of_split

end GroupApproximation.BooneHigman.Metabelian.Envelope
