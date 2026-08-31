import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeTailCoface

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace AffineBarycentricSubdivision

/-
**Every other face.** Restricting the cone along the `(j+1)`-th coface gives
the cone over the `j`-th face of `τ`.
-/
theorem cone_face_succ {n k : ℕ} (v : Delta n) (τ : Delta (k + 1) → Delta n)
    (j : Fin (k + 1 + 1)) :
    (fun y : Delta (k + 1) => affineConeMap v τ (cofaceTop (k + 1) j.succ y))
      = (fun y : Delta (k + 1) => affineConeMap v (fun z : Delta k => τ (cofaceTop k j z)) y) := by
  funext y;
  ext c;
  by_cases hy : ( y : Fin ( k + 1 + 1 ) → ℝ ) 0 = 1 <;> simp_all +decide [ affineConeMap_coord, cofaceTop_eq ];
  · simp +decide [ cofaceTop, stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply, Fin.succ_succAbove_zero ];
    rw [ Finset.sum_eq_single 0 ] <;> simp_all +decide [ Fin.succ_succAbove_zero ];
    intro b hb hb'; rw [ Fin.succAbove ] at hb; aesop;
  · rw [ show ( cofaceTop ( k + 1 ) j.succ ) y 0 = y 0 from ?_, coneTail_cofaceTop_succ j y hy ];
    unfold cofaceTop; simp +decide [ stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply, Fin.succ_succAbove_zero ] ;
    rw [ Finset.sum_eq_single 0 ] <;> simp +decide [ Fin.succ_succAbove_zero ];
    intro b hb hb'; rw [ Fin.succAbove ] at hb; aesop;
end AffineBarycentricSubdivision
end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

