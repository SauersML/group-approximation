import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwoInjective
import GroupApproximation.Meta.AxiomGuard

/-!
# The four root spans attached to an index `L` (lane sk-leavitt-23)

Over `𝔽₂ = ZMod 2`, fix an index `L`.  This file defines four root spans:

* `colSpan L = ⟨x_iL⟩` (the column `U`);
* `rowSpan L = ⟨x_Lj⟩` (the row `V`);
* `parSpan L = ⟨x_ij : j ≠ L⟩` (the stabilizer `P` of `e_L`);
* `levSpan L = ⟨x_ij : i ≠ L, j ≠ L⟩` (the Levi part `S`).

It proves that `levSpan L` normalizes `colSpan L` and `rowSpan L`.  It also proves that the
columns other than `b` normalize the `b`-th column span `⟨x_kb⟩`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo

open GroupApproximation.SteinbergGroup

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem two_eq_zero : (2 : ZMod 2) = 0 := by decide

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.two_eq_zero

/-- The column root span `⟨x_iL⟩`. -/
abbrev colSpan (L : I) : Subgroup (SteinbergGroup I (ZMod 2)) := rootSpan (fun _ j => j = L)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.colSpan

/-- The row root span `⟨x_Lj⟩`. -/
abbrev rowSpan (L : I) : Subgroup (SteinbergGroup I (ZMod 2)) := rootSpan (fun i _ => i = L)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.rowSpan

/-- The root span `⟨x_ij : j ≠ L⟩`. -/
abbrev parSpan (L : I) : Subgroup (SteinbergGroup I (ZMod 2)) := rootSpan (fun _ j => j ≠ L)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.parSpan

/-- The root span `⟨x_ij : i ≠ L, j ≠ L⟩`. -/
abbrev levSpan (L : I) : Subgroup (SteinbergGroup I (ZMod 2)) :=
  rootSpan (fun i j => i ≠ L ∧ j ≠ L)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.levSpan

theorem lev_le_par {L : I} {s : SteinbergGroup I (ZMod 2)} (hs : s ∈ levSpan L) :
    s ∈ parSpan L :=
  rootSpan_mono (p := fun i j => i ≠ L ∧ j ≠ L) (fun _ _ _ hp => hp.2) hs

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.lev_le_par

/-- `levSpan L` normalizes `colSpan L`. -/
theorem lev_conj_col {L : I} {s u : SteinbergGroup I (ZMod 2)} (hs : s ∈ levSpan L)
    (hu : u ∈ colSpan L) : s * u * s⁻¹ ∈ colSpan L := by
  refine rootSpan_normalizes ?_ hs hu
  intro i j h a hp k l h' b hq
  by_cases hkj : k = j
  · rw [WeylCalc.x_congr hkj hq h' hp.2 b, WeylCalc.conj_adj_left i j L h hp.2 hp.1 a b]
    exact Subgroup.mul_mem _ (x_mem_rootSpan _ _ rfl) (x_mem_rootSpan _ _ rfl)
  · rw [WeylCalc.conj_of_commute
      (x_commute_of_ne i j k l h h' (Ne.symm hkj) (by rw [hq]; exact hp.1.symm) a b)]
    exact x_mem_rootSpan _ _ hq

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.lev_conj_col

/-- `levSpan L` normalizes `rowSpan L`. -/
theorem lev_conj_row {L : I} {s v : SteinbergGroup I (ZMod 2)} (hs : s ∈ levSpan L)
    (hv : v ∈ rowSpan L) : s * v * s⁻¹ ∈ rowSpan L := by
  refine rootSpan_normalizes ?_ hs hv
  intro i j h a hp k l h' b hq
  by_cases hli : l = i
  · rw [WeylCalc.x_congr hq hli h' hp.1.symm b,
      WeylCalc.conj_adj_right L i j hp.1.symm h hp.2.symm b a]
    exact Subgroup.mul_mem _ (x_mem_rootSpan _ _ rfl) (x_mem_rootSpan _ _ rfl)
  · rw [WeylCalc.conj_of_commute
      (x_commute_of_ne i j k l h h' (by rw [hq]; exact hp.2) hli a b)]
    exact x_mem_rootSpan _ _ hq

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.lev_conj_row

/-- The column roots `x_iL` with `i ≠ b` normalize the `b`-th column span `⟨x_kb⟩`. -/
theorem colExcept_conj_colAt {L b : I} (hbL : b ≠ L) {u g : SteinbergGroup I (ZMod 2)}
    (hu : u ∈ rootSpan (R := ZMod 2) (fun i j => j = L ∧ i ≠ b))
    (hg : g ∈ rootSpan (R := ZMod 2) (fun _ l => l = b)) :
    u * g * u⁻¹ ∈ rootSpan (R := ZMod 2) (fun _ l => l = b) := by
  refine rootSpan_normalizes ?_ hu hg
  intro i j h a hp k l h' c hq
  have hiL : i ≠ L := by rw [← hp.1]; exact h
  by_cases hkL : k = L
  · rw [WeylCalc.x_congr rfl hp.1 h hiL a, WeylCalc.x_congr hkL hq h' hbL.symm c,
      WeylCalc.conj_adj_left i L b hiL hbL.symm hp.2 a c]
    exact Subgroup.mul_mem _ (x_mem_rootSpan _ _ rfl) (x_mem_rootSpan _ _ rfl)
  · rw [WeylCalc.conj_of_commute
      (x_commute_of_ne i j k l h h' (by rw [hp.1]; exact Ne.symm hkL)
        (by rw [hq]; exact hp.2.symm) a c)]
    exact x_mem_rootSpan _ _ hq

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.colExcept_conj_colAt

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo
