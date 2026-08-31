import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeTailFun

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace AffineBarycentricSubdivision

/-- The normalized tail of `x : Δᵏ⁺¹`, as a point of `Δᵏ`.  Away from the apex
(`x₀ = 1`) it is the genuine normalized tail; at the apex it is given an
irrelevant fallback value. -/
noncomputable def coneTail {k : ℕ} (x : Delta (k + 1)) : Delta k :=
  if h : (x : Fin (k + 1 + 1) → ℝ) 0 = 1 then stdSimplex.vertex (0 : Fin (k + 1))
  else ⟨coneTailFun x, coneTailFun_mem x h⟩

/-
Coordinate formula for `coneTail` away from the apex.
-/
theorem coneTail_apply {k : ℕ} (x : Delta (k + 1))
    (hx : (x : Fin (k + 1 + 1) → ℝ) 0 ≠ 1) (i : Fin (k + 1)) :
    (coneTail x : Fin (k + 1) → ℝ) i
      = (x : Fin (k + 1 + 1) → ℝ) i.succ / (1 - (x : Fin (k + 1 + 1) → ℝ) 0) := by
  unfold coneTail; aesop;

end AffineBarycentricSubdivision
end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
