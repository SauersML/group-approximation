import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeTail

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace AffineBarycentricSubdivision

noncomputable def affineConeMapFun {n k : ℕ} (v : Delta n) (τ : Delta k → Delta n)
    (x : Delta (k + 1)) : Fin (n + 1) → ℝ :=
  fun j => (x : Fin (k + 1 + 1) → ℝ) 0 * (v : Fin (n + 1) → ℝ) j
      + (1 - (x : Fin (k + 1 + 1) → ℝ) 0) * ((τ (coneTail x)) : Fin (n + 1) → ℝ) j

/-
The cone coordinate function always defines a point of `Δⁿ`.
-/
theorem affineConeMapFun_mem {n k : ℕ} (v : Delta n) (τ : Delta k → Delta n)
    (x : Delta (k + 1)) : affineConeMapFun v τ x ∈ stdSimplex ℝ (Fin (n + 1)) := by
  refine' ⟨ fun j => _, _ ⟩;
  · exact add_nonneg ( mul_nonneg ( stdSimplex.zero_le x 0 ) ( stdSimplex.zero_le v j ) ) ( mul_nonneg ( sub_nonneg.mpr ( stdSimplex.le_one x 0 ) ) ( stdSimplex.zero_le ( τ ( coneTail x ) ) j ) );
  · unfold affineConeMapFun;
    simp +decide [ Finset.sum_add_distrib, ← Finset.mul_sum _ _ _, stdSimplex.sum_eq_one ]

/-- **The affine cone map** `Cone_v(τ) : Δᵏ⁺¹ → Δⁿ`. -/
noncomputable def affineConeMap {n k : ℕ} (v : Delta n) (τ : Delta k → Delta n) :
    Delta (k + 1) → Delta n :=
  fun x => ⟨affineConeMapFun v τ x, affineConeMapFun_mem v τ x⟩

@[simp] theorem affineConeMap_coord {n k : ℕ} (v : Delta n) (τ : Delta k → Delta n)
    (x : Delta (k + 1)) (j : Fin (n + 1)) :
    (affineConeMap v τ x : Fin (n + 1) → ℝ) j
      = (x : Fin (k + 1 + 1) → ℝ) 0 * (v : Fin (n + 1) → ℝ) j
        + (1 - (x : Fin (k + 1 + 1) → ℝ) 0) * ((τ (coneTail x)) : Fin (n + 1) → ℝ) j := rfl

/-! ## 3. Vertex formulas -/

/-
The cone sends the apex vertex `0` to `v`.
-/
theorem affineConeMap_vertex_zero {n k : ℕ} (v : Delta n) (τ : Delta k → Delta n) :
    affineConeMap v τ (stdSimplex.vertex (0 : Fin (k + 1 + 1))) = v := by
  unfold affineConeMap; simp +decide [ stdSimplex.vertex ] ;
  unfold affineConeMapFun; simp +decide ;
  rfl

/-
The cone sends the vertex `i+1` to the vertex `τ(i)` of `τ`.
-/
theorem affineConeMap_vertex_succ {n k : ℕ} (v : Delta n) (τ : Delta k → Delta n)
    (i : Fin (k + 1)) :
    affineConeMap v τ (stdSimplex.vertex i.succ) = τ (stdSimplex.vertex i) := by
  ext j;
  rw [ affineConeMap_coord ] ; simp +decide [ Fin.succ_ne_zero ];
  congr;
  ext j; simp +decide [ coneTail_apply, stdSimplex.vertex ] ;
  simp +decide [ Pi.single_apply, Fin.ext_iff ]

/-! ## 4. Continuity and the bundled continuous cone map -/

/-
`coneTail` is continuous away from the apex.
-/

end AffineBarycentricSubdivision
end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
