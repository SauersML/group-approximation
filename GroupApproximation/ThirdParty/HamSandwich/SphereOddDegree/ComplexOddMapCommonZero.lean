import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.BorsukUlam
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.ComplexOddMapRealification
import GroupApproximation.Meta.AxiomGuard

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
  · refine ⟨⟨EuclideanSpace.single 0 1, by simp⟩, ?_⟩
    funext k
    exact Fin.elim0 (hm ▸ e.symm k)
  · have hd : 0 < d := by omega
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
    let g := complexOddMapRealification (n + 1) κ f
    obtain ⟨x, hx⟩ := borsuk_ulam g
    refine ⟨x, ?_⟩
    funext k
    let j : Fin m := e.symm k
    let ir : Fin (n + 1) := ⟨j, by omega⟩
    let ii : Fin (n + 1) := ⟨m + j, by omega⟩
    have hre : (f x k).re = (f (-x) k).re := by
      have h := congrArg (fun z : EuclideanSpace ℝ (Fin (n + 1)) => z ir) hx
      dsimp [g, ir] at h
      rw [complexOddMapRealification_real (n + 1) κ hdim f x j,
        complexOddMapRealification_real (n + 1) κ hdim f (-x) j] at h
      simpa [j, e] using h
    have him : (f x k).im = (f (-x) k).im := by
      have h := congrArg (fun z : EuclideanSpace ℝ (Fin (n + 1)) => z ii) hx
      dsimp [g, ii, m] at h
      rw [complexOddMapRealification_imag (n + 1) κ hdim f x j,
        complexOddMapRealification_imag (n + 1) κ hdim f (-x) j] at h
      simpa [j, e] using h
    have hre_odd : (f (-x) k).re = -(f x k).re := by
      simpa using congrArg Complex.re (congrFun (hf x) k)
    have him_odd : (f (-x) k).im = -(f x k).im := by
      simpa using congrArg Complex.im (congrFun (hf x) k)
    apply Complex.ext
    · change (f x k).re = 0
      linarith
    · change (f x k).im = 0
      linarith

/-! ## Closed audit endpoint -/

/-- **Closed endpoint for the complex-coordinate common-zero theorem.**

This is the shape STW Problem XXII consumes: an odd continuous map of the unit
sphere of `R^{d+1}` into `κ → ℂ` must vanish somewhere once the real dimension
`2 * card κ` of the target fits inside `d`.  Stated with no construction data,
paired with the sphere form it rests on, so `#audit_closed_axioms` certifies
that neither carries a hypothesis binder. -/
theorem complexOddMapCommonZero_closed :
    (∀ (d : ℕ) (κ : Type) (_ : Finite κ), 2 * Nat.card κ ≤ d →
        ∀ f : C(Sphere d, κ → ℂ), (∀ x : Sphere d, f (-x) = -f x) →
          ∃ x : Sphere d, f x = 0) ∧
    (∀ (n : ℕ) (g : C(Sphere (n + 1), Sphere n)),
        (∀ x, g (-x) = - g x) → False) :=
  ⟨fun d κ hκ hdim f hf => @complexOddMapCommonZero d κ hκ hdim f hf,
    no_odd_map_sphere_succ⟩

#audit_closed_axioms complexOddMapCommonZero_closed

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
