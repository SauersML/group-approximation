import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.Basic

/-!
# Realification of finite complex-coordinate maps

This module packages the continuous real-coordinate map used to pass from a
finite complex target to the Euclidean target in Borsuk--Ulam.
-/

noncomputable section

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

private def complexOddMapRealCoord
    (d : ℕ) (κ : Type) [Finite κ] (f : C(Sphere d, κ → ℂ))
    (x : Sphere d) (i : Fin d) : ℝ :=
  if hi : (i : ℕ) < Nat.card κ then
    (f x ((Finite.equivFin κ).symm ⟨i, hi⟩)).re
  else if hi' : (i : ℕ) < 2 * Nat.card κ then
    (f x ((Finite.equivFin κ).symm ⟨(i : ℕ) - Nat.card κ, by omega⟩)).im
  else 0

/-- A finite complex-coordinate map, written in real and imaginary coordinates
and padded by zeroes to a `d`-dimensional Euclidean target. -/
def complexOddMapRealification
    (d : ℕ) (κ : Type) [Finite κ] (f : C(Sphere d, κ → ℂ)) :
    C(Sphere d, EuclideanSpace ℝ (Fin d)) := {
  toFun := fun x =>
    (WithLp.equiv 2 (Fin d → ℝ)).symm (complexOddMapRealCoord d κ f x)
  continuous_toFun := by
    have hcoord : Continuous (complexOddMapRealCoord d κ f) := by
      apply continuous_pi
      intro i
      unfold complexOddMapRealCoord
      split_ifs <;> fun_prop
    exact continuous_induced_rng.mpr hcoord }

@[simp]
theorem complexOddMapRealification_real
    (d : ℕ) (κ : Type) [Finite κ] (hdim : 2 * Nat.card κ ≤ d)
    (f : C(Sphere d, κ → ℂ)) (x : Sphere d) (j : Fin (Nat.card κ)) :
    complexOddMapRealification d κ f x ⟨j, by omega⟩ =
      (f x ((Finite.equivFin κ).symm j)).re := by
  change complexOddMapRealCoord d κ f x ⟨j, by omega⟩ = _
  rw [complexOddMapRealCoord, dif_pos j.isLt]

@[simp]
theorem complexOddMapRealification_imag
    (d : ℕ) (κ : Type) [Finite κ] (hdim : 2 * Nat.card κ ≤ d)
    (f : C(Sphere d, κ → ℂ)) (x : Sphere d) (j : Fin (Nat.card κ)) :
    complexOddMapRealification d κ f x
        ⟨Nat.card κ + j, by omega⟩ =
      (f x ((Finite.equivFin κ).symm j)).im := by
  change complexOddMapRealCoord d κ f x ⟨Nat.card κ + j, by omega⟩ = _
  have hnlt : ¬Nat.card κ + (j : ℕ) < Nat.card κ := by omega
  have hlt : Nat.card κ + (j : ℕ) < 2 * Nat.card κ := by omega
  rw [complexOddMapRealCoord, dif_neg hnlt, dif_pos hlt]
  have hfin :
      (⟨Nat.card κ + (j : ℕ) - Nat.card κ, by omega⟩ : Fin (Nat.card κ)) = j := by
    ext
    simp
  rw [hfin]

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
