import GroupApproximation.CharClass.LerayHirschCompactOf
import GroupApproximation.CharClass.GysinTautChartOf
import GroupApproximation.CharClass.GysinPairRetractOf
import GroupApproximation.CharClass.GysinRanged
import GroupApproximation.CharClass.GysinFromGraded
import GroupApproximation.CharClass.ProjectiveSpaceRingClosed
import GroupApproximation.CharClass.ProjectiveSpaceComputationOf
import GroupApproximation.CharClass.CohomologyTotalNontrivialOf

/-!
# The powers of a degree-two class of `ℂP^d` over a field are nonzero

The coefficient-generic form of `ProjectiveSpaceRingBootstrap.cupPowE_cpGen_ne_zero_of_chart`: for a
field `K` and any nonzero `h ∈ H^2(ℂP^d; K)`, `h^m ≠ 0` for every `m ≤ d`.  This is the ring input of
the general-rank Leray–Hirsch ladder over `K`.

The argument is the `F₂` one.  The Gysin step (`GysinRanged.cupPowE_ne_zero_of_pieces`, generic)
runs on `P(taut ⊕ 1) → ℂP^d` against the tautological class `tautEulerOfK K hgen (cpTaut d).plusOne`,
with inputs over `K`:

* rank-two Leray–Hirsch over a compact base, `lerayHirschGraded_compactOf_of_freeTuple` at `s = 2`,
  whose only input is the free tuple of `U × ℂP^1`;
* the two readings `rChartOf`, `rNotZeroOf` and their multiplicativity (`GysinRetractOf`);
* the chart reading kills the tautological class (`GysinTautChartOf`; the class there, `tautEulerK`,
  is `tautEulerOfK` of `p ⊕ 1` by definition);
* the pair of readings is bijective in degrees `2` to `2d` (`GysinPairRetractOf`).

It produces a class `e` whose powers up to `d` are nonzero.  `H^2(ℂP^d; K)` is a line
(`hasCPCohomologyOf_CP`), so every nonzero `h` is a unit multiple of `e`, and `h^m = c^m e^m ≠ 0`.
No generator is identified at any point.

## Main declarations

* `cupPowE_smulOf` — the powers of a scalar multiple.
* `cupPowE_rNotZero_ne_zeroOf_of_freeTuple` — the Gysin step over `K`.
* `cupPowE_ne_zeroOf_of_freeTuple` — **every nonzero class has nonzero powers**, over the rank-two
  free tuple.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace CPn

open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.CharClass.Bundle

noncomputable section

/-- **The cup powers of a scalar multiple.** -/
theorem cupPowE_smulOf {K : Type} [CommRing K] {X : TopCat.{0}} (c : K) (e : Hmod K X 2)
    (m : ℕ) : cupPowE (c • e) m = c ^ m • cupPowE e m := by
  induction m with
  | zero => simp only [cupPowE_zero, pow_zero, one_smul]
  | succ m ih =>
    rw [cupPowE_succ, cupPowE_succ, ih, cup_smul_left, cup_smul_right, smul_smul, pow_succ]

/-- The projectivised sum of the tautological line with a trivial line has rank two. -/
theorem rank_plusOne_cpTaut (d : ℕ) (z : CP d) : (cpTaut d).plusOne.rank z = 2 := by
  have h1 : (cpTaut d).rank z = 1 := by
    have h := trace_eq_rank (cpTaut d) z
    rw [trace_cpTaut] at h
    exact_mod_cast h.symm
  rw [rank_plusOne, h1]

set_option maxHeartbeats 400000 in
/-- **The Gysin step over a field.**  The complement's reading of the tautological class of
`P(taut ⊕ 1)` has nonzero powers up to the dimension, for every nonzero `hgen`, over the free tuple
of `U × ℂP^1`. -/
theorem cupPowE_rNotZero_ne_zeroOf_of_freeTuple (K : Type) [Field K] (d : ℕ) (hd : 1 ≤ d)
    (hgen : Hmod K (CPtop (1 + LH.tautCardOf (Fin (d + 1) ⊕ Unit))) 2) (hgen0 : hgen ≠ 0)
    (hfree : ∀ (U : Type) [TopologicalSpace U] (hfib : Hmod K (CPtop 1) 2), hfib ≠ 0 →
      LH.HasFreeTuple (KnCP.cpFst U 1) (pull (KnCP.cpSnd U 1) 2 hfib) 2)
    {m : ℕ} (hm : m ≤ d) :
    cupPowE (Gysin.rNotZeroOf K (cpTaut d) (trace_cpTaut d) 2
      (LH.tautEulerOfK K hgen (cpTaut d).plusOne)) m ≠ 0 := by
  have L : LerayHirschGraded (Gysin.gysinProj (cpTaut d))
      (LH.tautEulerOfK K hgen (cpTaut d).plusOne) 2 :=
    LH.lerayHirschGraded_compactOf_of_freeTuple K (cpTaut d).plusOne 2
      (rank_plusOne_cpTaut d) (by norm_num) hgen hgen0
      (by
        intro U _ d' hd' hfib hfib0
        obtain rfl : d' = 0 := by omega
        exact hfree U hfib hfib0)
  have hz : Gysin.rChartOf K (cpTaut d) 2 (LH.tautEulerOfK K hgen (cpTaut d).plusOne) = 0 :=
    Gysin.rChartOf_tautEulerK K (cpTaut d) (Gysin.isZeroSectionChart (cpTaut d)) hgen
  refine Gysin.cupPowE_ne_zero_of_pieces (Gysin.gysinProj (cpTaut d))
    (LH.tautEulerOfK K hgen (cpTaut d).plusOne)
    (Gysin.rChartOf K (cpTaut d)) (Gysin.rNotZeroOf K (cpTaut d) (trace_cpTaut d))
    (Gysin.rChartOf_pull (cpTaut d)) (Gysin.rNotZeroOf_pull (cpTaut d) (trace_cpTaut d))
    ?_ ?_ d ?_ ?_ ?_ (one_ne_zero_cohZeroOf K (CPtop d)) hm
  · intro k b
    rw [Gysin.rChartOf_cup, hz, cup_zero]
  · intro k b
    exact Gysin.rNotZeroOf_cup (cpTaut d) (trace_cpTaut d) k b _
  · intro j hj
    exact Gysin.bijective_pair_cpTautOf K d j hj
  · intro n z
    exact LH.lh_surj_of_graded L n z
  · intro n a b h
    exact LH.lh_uniq_of_graded L n a b h

/-- **Some class in degree two of `ℂP^d` has nonzero powers up to the dimension**, over a field,
over the free tuple of `U × ℂP^1`. -/
theorem exists_cupPowE_ne_zeroOf_of_freeTuple (K : Type) [Field K]
    (hfree : ∀ (U : Type) [TopologicalSpace U] (hfib : Hmod K (CPtop 1) 2), hfib ≠ 0 →
      LH.HasFreeTuple (KnCP.cpFst U 1) (pull (KnCP.cpSnd U 1) 2 hfib) 2)
    (d : ℕ) (hd : 1 ≤ d) :
    ∃ e : Hmod K (CPtop d) 2, ∀ j : ℕ, j ≤ d → cupPowE e j ≠ 0 := by
  obtain ⟨φN⟩ : Nonempty (Hmod K (CPtop (1 + LH.tautCardOf (Fin (d + 1) ⊕ Unit))) 2 ≃ₗ[K] K) :=
    (hasCPCohomologyOf_CP K (1 + LH.tautCardOf (Fin (d + 1) ⊕ Unit))).1 1 (by omega)
  have hgen0 : φN.symm 1 ≠ 0 := fun h => by simpa using congrArg φN h
  exact ⟨_, fun j hj =>
    cupPowE_rNotZero_ne_zeroOf_of_freeTuple K d hd (φN.symm 1) hgen0 hfree hj⟩

/-- **Every nonzero degree-two class of `ℂP^d` has nonzero powers up to the dimension**, over a
field, over the free tuple of `U × ℂP^1`.  `H^2(ℂP^d; K)` is a line, so `h` is a unit multiple of the
class the Gysin step produces. -/
theorem cupPowE_ne_zeroOf_of_freeTuple (K : Type) [Field K]
    (hfree : ∀ (U : Type) [TopologicalSpace U] (hfib : Hmod K (CPtop 1) 2), hfib ≠ 0 →
      LH.HasFreeTuple (KnCP.cpFst U 1) (pull (KnCP.cpSnd U 1) 2 hfib) 2)
    (d : ℕ) (hd : 1 ≤ d) (h : Hmod K (CPtop d) 2) (h0 : h ≠ 0) {m : ℕ} (hm : m ≤ d) :
    cupPowE h m ≠ 0 := by
  obtain ⟨e, hpow⟩ := exists_cupPowE_ne_zeroOf_of_freeTuple K hfree d hd
  have he0 : e ≠ 0 := by
    have h1 := hpow 1 hd
    rwa [LH.cupPowE_oneOf] at h1
  obtain ⟨φ⟩ : Nonempty (Hmod K (CPtop d) 2 ≃ₗ[K] K) := (hasCPCohomologyOf_CP K d).1 1 hd
  have hφe : φ e ≠ 0 := fun hz => he0 (φ.injective (by rw [hz, map_zero]))
  have hφh : φ h ≠ 0 := fun hz => h0 (φ.injective (by rw [hz, map_zero]))
  have hh : h = (φ h * (φ e)⁻¹) • e := by
    apply φ.injective
    rw [map_smul, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hφe, mul_one]
  have hc : φ h * (φ e)⁻¹ ≠ 0 := mul_ne_zero hφh (inv_ne_zero hφe)
  rw [hh, cupPowE_smulOf]
  intro hz
  apply hpow m hm
  rw [← inv_smul_smul₀ (pow_ne_zero m hc) (cupPowE e m), hz, smul_zero]

end

end CPn
end CharClass
end GroupApproximation
