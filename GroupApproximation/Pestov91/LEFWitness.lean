import GroupApproximation.Pestov91.LEFCrossedProduct
import GroupApproximation.Pestov91.WitnessRing
import GroupApproximation.Pestov91.ToeplitzModel
import GroupApproximation.Pestov91.WitnessCentre

/-!
# The Pestov 9.1 witness ring is an LEF ring

`WitnessRing = LC(X, 𝔽₂) ⋊ ℤ`, where `X` is the Toeplitz subshift. A finite part of the ring is
modelled on the cycle `ℤ/N`. A locally constant function `a` goes to its values `a (w n)` at points
`w n` of `X` that realise the windows of a periodic model `p : ℤ/N → Bool` of the subshift
(`exists_periodic_model`). The function `a` depends only on the coordinates in `[-r, r]`
(`exists_radius`), so the shift of `X` becomes the rotation of `ℤ/N`. Every window of `X` occurs in
`p`, so a nonzero `a` stays nonzero.

* `evalAlong`: evaluation of locally constant functions along a family of points;
* `witnessRing_isLEFRing`: `WitnessRing` is an LEF ring, by `isLEFRing_skewMonoidAlgebra_of_periodic`;
* `isLEF_elementaryGroup_witnessRing`: `EL₃(WitnessRing)` is LEF;
* `isLEF_elementaryModCentre_witnessRing`: `EL₃(WitnessRing)` modulo its centre is LEF.
-/

namespace GroupApproximation
namespace Pestov91

open Multiplicative (toAdd)

/-- Evaluation of locally constant functions along a family of points `w`. -/
def evalAlong {ι : Type*} {K : Type*} [Semiring K] (w : ι → X) :
    LocallyConstant X K →+* (ι → K) where
  toFun a n := a (w n)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem evalAlong_apply {ι : Type*} {K : Type*} [Semiring K] (w : ι → X)
    (a : LocallyConstant X K) (n : ι) : evalAlong w a n = a (w n) :=
  rfl

/-- **The Pestov 9.1 witness ring is an LEF ring.** -/
theorem witnessRing_isLEFRing : IsLEFRing WitnessRing := by
  refine isLEFRing_skewMonoidAlgebra_of_periodic fun T B ↦ ?_
  choose r hr using fun a : LocallyConstant X (ZMod 2) ↦ exists_radius a
  obtain ⟨ρ, hρr, hρB⟩ : ∃ ρ : ℕ, (∀ a ∈ T, r a + B ≤ ρ) ∧ B ≤ ρ :=
    ⟨T.sup r + B, fun a ha ↦ by have h := Finset.le_sup (f := r) ha; omega,
      Nat.le_add_left _ _⟩
  obtain ⟨N, hN, p, hmodel, hcover⟩ := exists_periodic_model ρ
  choose w hw using hmodel
  refine ⟨ZMod 2, inferInstance, inferInstance, N, ⟨by omega⟩, evalAlong w, by omega,
    fun a ha hne hD ↦ hne ?_, fun a ha g hg n ↦ ?_⟩
  · ext y
    obtain ⟨n, hn⟩ := hcover y
    have hya : a y = a (w n) := hr a y (w n) fun k hk ↦ by
      have hra := hρr a ha
      obtain ⟨hk1, hk2⟩ := abs_le.mp hk
      have hkρ : |k| ≤ ρ := abs_le.mpr ⟨by omega, by omega⟩
      rw [hn k hkρ, hw n k hkρ]
    exact hya.trans (congrFun hD n)
  · show a (shiftBy (-toAdd g) (w n)) = a (w (n - (toAdd g : ℤ)))
    refine hr a _ _ fun k hk ↦ ?_
    obtain ⟨hg1, hg2⟩ := abs_le.mp hg
    obtain ⟨hk1, hk2⟩ := abs_le.mp hk
    have hra := hρr a ha
    rw [shiftBy_apply, hw n (-toAdd g + k) (abs_le.mpr ⟨by omega, by omega⟩),
      hw (n - (toAdd g : ℤ)) k (abs_le.mpr ⟨by omega, by omega⟩)]
    congr 1
    push_cast
    ring

/-- **`EL₃` of the witness ring is LEF.** -/
theorem isLEF_elementaryGroup_witnessRing : IsLEF ↥(elementaryGroup (Fin 3) WitnessRing) :=
  isLEF_elementaryGroup witnessRing_isLEFRing

/-- **`EL₃` of the witness ring modulo its centre is LEF.** The central elements of the witness
ring are `0` and `1`, by `CrossedProduct.central_zero_or_one_of_free_minimal`. -/
theorem isLEF_elementaryModCentre_witnessRing :
    IsLEF (↥(elementaryGroup (Fin 3) WitnessRing) ⧸
      Subgroup.center ↥(elementaryGroup (Fin 3) WitnessRing)) := by
  refine isLEF_elementaryModCentre_of_central_zero_or_one witnessRing_isLEFRing fun c hc ↦ ?_
  refine CrossedProduct.central_zero_or_one_of_free_minimal (fun j ↦ shiftBy (-j))
    (fun _ hj x ↦ shiftBy_ne_self x (neg_ne_zero.mpr hj)) (fun x ↦ ?_)
    (fun j f x ↦ witnessAction_apply j f x) c hc
  have h : (Set.range fun j : ℤ ↦ shiftBy (-j) x) = Set.range fun j : ℤ ↦ shiftBy j x :=
    Set.ext fun _ ↦ ⟨fun ⟨j, hj⟩ ↦ ⟨-j, hj⟩,
      fun ⟨j, hj⟩ ↦ ⟨-j, by simpa only [neg_neg] using hj⟩⟩
  rw [h]
  exact dense_range_shiftBy x

end Pestov91
end GroupApproximation
