import GroupApproximation.StableRange.Krull
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Localization.Away.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Bass's bound for the rings of the metabelian chain

Lane `fix-bh-a`.  These follow from `stableRangeLE_of_ringKrullDim_le` (`StableRange.Krull`)
and Mathlib's dimension formula `MvPolynomial.ringKrullDim_of_isNoetherianRing`.

* `ringKrullDim_le_of_isLocalization`: localization does not raise Krull dimension.
* `stableRangeLE_mvPolynomial_of_isNoetherianRing`: `sr(A[s₁, …, s_k]) ≤ e + k + 1` for noetherian
  `A` with `dim A ≤ e`.
* `stableRangeLE_mvPolynomial_away`: `sr(ℤ[1/m][s₁, …, s_k]) ≤ k + 2` for every `m`.  These are the
  rings of Z1 (`Localization.Away (m : ℤ)`, as in `ElemFPCharZeroK2NilEndpoint`).  The case `k = 0`
  is `sr(ℤ[1/m]) ≤ 2`.

For `F_p[s₁, …, s_k]` the sharper `sr ≤ k + 1` is already on main (`vdkSR_polyStableRange`,
lane `bh-met-90m`), and is also the case `e = 0` of the noetherian bound.
-/

namespace GroupApproximation.StableRange

open GroupApproximation.BooneHigman.Metabelian.ElemFP

/-- Localization does not raise Krull dimension: `Spec S` embeds into `Spec R` as an order. -/
theorem ringKrullDim_le_of_isLocalization {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] : ringKrullDim S ≤ ringKrullDim R :=
  Order.krullDim_le_of_strictMono
    (fun J ↦ (⟨Ideal.comap (algebraMap R S) J.asIdeal, inferInstance⟩ : PrimeSpectrum R))
    (Monotone.strictMono_of_injective (fun _ _ hab ↦ Ideal.comap_mono hab)
      (fun J J' h ↦ PrimeSpectrum.ext <| by
        have h' : Ideal.comap (algebraMap R S) J.asIdeal =
            Ideal.comap (algebraMap R S) J'.asIdeal := congrArg PrimeSpectrum.asIdeal h
        rw [← IsLocalization.map_under M S J.asIdeal, ← IsLocalization.map_under M S J'.asIdeal]
        exact congrArg (Ideal.map (algebraMap R S)) h'))

#audit_axioms GroupApproximation.StableRange.ringKrullDim_le_of_isLocalization

/-- **Bass's bound** for polynomial rings over a noetherian ring:
`sr(A[s₁, …, s_k]) ≤ dim A + k + 1`. -/
theorem stableRangeLE_mvPolynomial_of_isNoetherianRing (A : Type*) [CommRing A]
    [IsNoetherianRing A] {e : ℕ} (he : ringKrullDim A ≤ e) (k : ℕ) :
    vdkStab_StableRangeLE (MvPolynomial (Fin k) A) (e + k + 1) := by
  apply stableRangeLE_of_ringKrullDim_le
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.cast_add]
  exact add_le_add_right he _

#audit_axioms GroupApproximation.StableRange.stableRangeLE_mvPolynomial_of_isNoetherianRing

/-- `dim ℤ ≤ 1`. -/
theorem ringKrullDim_int_le_one : ringKrullDim ℤ ≤ 1 := by
  rw [← Nat.cast_one, ← Ring.krullDimLE_iff]
  infer_instance

#audit_axioms GroupApproximation.StableRange.ringKrullDim_int_le_one

/-- `dim ℤ[1/m] ≤ 1`. -/
theorem ringKrullDim_away_le_one (m : ℕ) : ringKrullDim (Localization.Away (m : ℤ)) ≤ 1 :=
  (ringKrullDim_le_of_isLocalization (Submonoid.powers (m : ℤ))).trans ringKrullDim_int_le_one

#audit_axioms GroupApproximation.StableRange.ringKrullDim_away_le_one

/-- **`sr(ℤ[1/m][s₁, …, s_k]) ≤ k + 2`** for every `m` and `k`. -/
theorem stableRangeLE_mvPolynomial_away (m k : ℕ) :
    vdkStab_StableRangeLE (MvPolynomial (Fin k) (Localization.Away (m : ℤ))) (k + 2) := by
  haveI : IsNoetherianRing (Localization.Away (m : ℤ)) :=
    IsLocalization.isNoetherianRing (Submonoid.powers (m : ℤ)) _ inferInstance
  have h := stableRangeLE_mvPolynomial_of_isNoetherianRing (Localization.Away (m : ℤ)) (e := 1)
    (by exact_mod_cast ringKrullDim_away_le_one m) k
  rwa [show 1 + k + 1 = k + 2 by omega] at h

#audit_axioms GroupApproximation.StableRange.stableRangeLE_mvPolynomial_away

end GroupApproximation.StableRange
