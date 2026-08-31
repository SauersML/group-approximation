import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.BorsukUlam

/-!
# Complex-coordinate Borsuk--Ulam

This file converts the real-coordinate statement `borsuk_ulam` into the exact
finite complex-coordinate common-zero theorem used by the operator-algebraic
counterexample.  A map to `κ → ℂ` is realified into its real and imaginary
coordinates and padded by zeroes to the ambient sphere dimension.
-/

noncomputable section

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- An odd continuous map `S^d → ℂ^κ` has a zero whenever the real dimension
`2 * card κ` of its target is at most `d`. -/
theorem complexOddMapCommonZero
    (d : ℕ) (κ : Type) [Finite κ] (hdim : 2 * Nat.card κ ≤ d)
    (f : C(Sphere d, κ → ℂ))
    (hf : ∀ x : Sphere d, f (-x) = -f x) :
    ∃ x : Sphere d, f x = 0 := by
  let m := Nat.card κ
  let e : Fin m ≃ κ := (Finite.equivFin κ).symm
  by_cases hm : m = 0
  · refine ⟨northPole d, ?_⟩
    funext k
    exact Fin.elim0 (hm ▸ e.symm k)
  · have hd : 0 < d := by omega
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
    let g : C(Sphere (n + 1), EuclideanSpace ℝ (Fin (n + 1))) where
      toFun x i :=
        if hi : (i : ℕ) < m then
          (f x (e ⟨i, hi⟩)).re
        else if hi' : (i : ℕ) < 2 * m then
          (f x (e ⟨(i : ℕ) - m, by omega⟩)).im
        else 0
      continuous_toFun := by
        apply continuous_pi
        intro i
        split_ifs <;> fun_prop
    obtain ⟨x, hx⟩ := borsuk_ulam g
    refine ⟨x, ?_⟩
    funext k
    let j : Fin m := e.symm k
    let ir : Fin (n + 1) := ⟨j, by omega⟩
    let ii : Fin (n + 1) := ⟨m + j, by omega⟩
    have hre : (f x k).re = (f (-x) k).re := by
      have h := congrFun hx ir
      simpa [g, ir, j, e] using h
    have him : (f x k).im = (f (-x) k).im := by
      have h := congrFun hx ii
      simpa [g, ii, j, e] using h
    have hre_odd : (f (-x) k).re = -(f x k).re := by
      simpa using congrArg Complex.re (congrFun (hf x) k)
    have him_odd : (f (-x) k).im = -(f x k).im := by
      simpa using congrArg Complex.im (congrFun (hf x) k)
    apply Complex.ext
    · simp only [Complex.zero_re]
      linarith
    · simp only [Complex.zero_im]
      linarith

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
