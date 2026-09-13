import GroupApproximation.Pestov91.WitnessRing
import GroupApproximation.Pestov91.SubshiftMinimal
import GroupApproximation.Pestov91.RingSimple
import GroupApproximation.Pestov91.SplitSimplicity
import GroupApproximation.Pestov91.WitnessCentre
import GroupApproximation.Pestov91.CentreSkew
import Mathlib.Algebra.Field.ZMod

/-!
# Simplicity of `EL₃` over the Pestov 9.1 witness ring

`WitnessRing = LC(X, 𝔽₂) ⋊ ℤ`, where `ofAdd j` acts by `f ↦ f ∘ shiftBy (-j)`.  So the dynamics
of `RingSimple` and `WitnessCentre` is `τ j = shiftBy (-j)`.

* `witness_free`, `witness_minimal`: `τ` is free, and every orbit is dense.
* `witnessRing_central_zero_or_one`: the central elements are `0` and `1`.
* `witnessRing_isSimpleRing`: the ring is simple.
* `isSimpleGroup_elementaryGroup_witnessRing`: `EL₃(WitnessRing)` is simple.  The split
  condition comes from `locallyConstant_cut_key`.

The prose of this module was written by Claude (Anthropic).
-/

namespace GroupApproximation

namespace Pestov91

open Multiplicative (ofAdd)

/-- The shift of the witness action has no periodic points. -/
theorem witness_free : ∀ j : ℤ, j ≠ 0 → ∀ x : X, shiftBy (-j) x ≠ x :=
  fun _ hj x => shiftBy_ne_self x (neg_ne_zero.mpr hj)

/-- Every orbit of the witness action is dense. -/
theorem witness_minimal (x : X) : Dense (Set.range fun j : ℤ => shiftBy (-j) x) := by
  have h : (Set.range fun j : ℤ => shiftBy (-j) x) = Set.range fun n : ℤ => shiftBy n x :=
    Set.ext fun _ => ⟨fun ⟨j, hj⟩ => ⟨-j, hj⟩,
      fun ⟨n, hn⟩ => ⟨-n, by simpa only [neg_neg] using hn⟩⟩
  rw [h]
  exact dense_range_shiftBy x

/-- **The centre of the witness ring is `{0, 1}`.** -/
theorem witnessRing_central_zero_or_one (c : WitnessRing)
    (hc : ∀ r : WitnessRing, r * c = c * r) : c = 0 ∨ c = 1 :=
  CrossedProduct.central_zero_or_one_of_free_minimal (fun j => shiftBy (-j)) witness_free
    witness_minimal (fun j f x => witnessAction_apply j f x) c hc

/-- **The witness ring is simple.** -/
instance witnessRing_isSimpleRing : IsSimpleRing WitnessRing :=
  haveI : Nontrivial (ZMod 2) := nontrivial_of_ne (0 : ZMod 2) 1 (by decide)
  haveI : Nontrivial (LocallyConstant X (ZMod 2)) := locallyConstant_nontrivial
  isSimpleRing_of_minimal_free (K := ZMod 2) CrossedProduct.C CrossedProduct.unit
    (fun j => shiftBy (-j)) (fun j => (shiftBy (-j)).continuous) witness_free witness_minimal
    (fun j a => ofAdd j • a) (fun j f x => witnessAction_apply j f x)
    CrossedProduct.unit_zpow_mul_C CrossedProduct.exists_sum_C_mul_unit_zpow

/-- **`EL₃` of the witness ring is simple.** -/
theorem isSimpleGroup_elementaryGroup_witnessRing :
    IsSimpleGroup ↥(elementaryGroup (Fin 3) WitnessRing) :=
  isSimpleGroup_elementaryGroup_crossedProduct (Fintype.card_fin 3).symm.le
    witnessRing_central_zero_or_one CrossedProduct.C CrossedProduct.unit
    (fun j a => ofAdd j • a) CrossedProduct.unit_zpow_mul_C
    CrossedProduct.exists_sum_C_mul_unit_zpow
    (locallyConstant_cut_key (fun j => shiftBy (-j)) (fun j => (shiftBy (-j)).continuous)
      witness_free
      (fun _ hW hne => exists_finset_cover_of_dense_orbits (fun j => shiftBy (-j))
        (fun j => (shiftBy (-j)).continuous) witness_minimal hW hne)
      (fun j a => ofAdd j • a) (fun j f x => witnessAction_apply j f x))

end Pestov91

end GroupApproximation
