/-
Local adaptation of the HamSandwich development at
https://github.com/akopjan/HamSandwich/tree/76202dbbb6610ffcebbccfbf7a56f833a4c2a376
Changed for this repository: namespace isolation, Lean 4.32 porting,
and local proof integration. The original license is retained in this tree.
-/
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeTailFunDef

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace AffineBarycentricSubdivision

theorem coneTailFun_mem {k : ℕ} (x : Delta (k + 1))
    (hx : (x : Fin (k + 1 + 1) → ℝ) 0 ≠ 1) :
    coneTailFun x ∈ stdSimplex ℝ (Fin (k + 1)) := by
  refine' ⟨ fun i => _, _ ⟩;
  · exact div_nonneg ( x.2.1 _ ) ( sub_nonneg.2 ( x.2.2 ▸ Finset.single_le_sum ( fun a _ => x.2.1 a ) ( Finset.mem_univ 0 ) ) );
  · have h_sum : ∑ i : Fin (k + 1), (x : Fin (k + 1 + 1) → ℝ) i.succ = 1 - (x : Fin (k + 1 + 1) → ℝ) 0 := by
      apply eq_sub_of_add_eq'
      rw [← Fin.sum_univ_succ]
      exact x.2.2
    unfold coneTailFun;
    rw [ ← Finset.sum_div, h_sum, div_self ( sub_ne_zero_of_ne <| Ne.symm hx ) ]

end AffineBarycentricSubdivision
end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
