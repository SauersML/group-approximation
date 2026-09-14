/-
Local adaptation of the HamSandwich development at
https://github.com/akopjan/HamSandwich/tree/76202dbbb6610ffcebbccfbf7a56f833a4c2a376
Changed for this repository: namespace isolation, Lean 4.32 porting,
and local proof integration. The original license is retained in this tree.
-/
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RealProjectiveSpace
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.HomotopyToChainHomotopy
































open CategoryTheory AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- Any two points of `Sphere 0` (the unit sphere in `ℝ¹`) are equal or
antipodal: the one-dimensional unit sphere is the two-point set `{±e}`. -/
theorem sphere_zero_eq_or_neg (x y : Sphere 0) : x = y ∨ x = -y := by
  rcases x with ⟨x, hx⟩; rcases y with ⟨y, hy⟩
  simp_all +decide
  rw [mem_sphere_zero_iff_norm] at hx hy
  norm_num [EuclideanSpace.norm_eq] at hx hy
  simp_all +decide [Fin.eq_zero, Subtype.ext_iff]
  cases hx <;> cases hy <;> simp_all +decide
  · exact Or.inl (by ext i; fin_cases i; aesop)
  · exact Or.inr (by ext i; fin_cases i; aesop)
  · exact Or.inr (by ext i; fin_cases i; aesop)
  · exact Or.inl (by ext i; fin_cases i; aesop)

/-- `RP⁰` is a single point: the antipodal quotient of the two-point set
`Sphere 0`. -/
instance : Subsingleton (RP 0) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, rfl⟩ := RP.exists_rep a
  obtain ⟨y, rfl⟩ := RP.exists_rep b
  simp +decide
  exact sphere_zero_eq_or_neg x y

/-- `RP⁰` is nonempty (it is the image of the nonempty `Sphere 0`). -/
instance : Nonempty (RP 0) :=
  ⟨proj 0 ⟨EuclideanSpace.single 0 1, by norm_num [EuclideanSpace.norm_eq]⟩⟩

/-- **Higher singular homology of `RP⁰` vanishes.** For `n ≠ 0`,
`Hₙ(RP⁰; ℤ) = 0`, since `RP⁰` is totally disconnected (a point). -/
theorem rp0_singularHomologyℤ_isZero (n : ℕ) (hn : n ≠ 0) :
    Limits.IsZero ((singularHomologyℤ n).obj (TopCat.of (RP 0))) :=
  AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat ℤ) n (ModuleCat.of ℤ ℤ) (TopCat.of (RP 0)) hn

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree