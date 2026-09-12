import GroupApproximation.CharClass.CohomologyKunnethTorusOf
import GroupApproximation.CharClass.CohomologyParityKunneth
import GroupApproximation.CharClass.LIXStepDGenParity
import GroupApproximation.Meta.AxiomGuard

/-!
# Künneth for the two sphere factors of the mapping-torus base at rank `n`, mod 2

Lane `lx-kunneth` of the STW Problem LIX strengthening (`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`
§1.4; residual (b) of `Gen.lemmaTwoFor_powers_two_lixChernOf`, the fields `tx_inj` and `gamma_eq`
of `Gen.WuStepDData`).

`CharClass/CohomologyParityKunneth.lean` proves, at rank two, that the `t x`-coordinate of a class
on `(Y × S⁵) × S¹` is well defined and that an even class splits into a pullback from `Y` plus a
`t x`-multiple once `Y` has no odd cohomology.  Nothing there uses the dimension of the odd sphere
except through the degree bookkeeping, so this file restates both over the rank-`n` model
`KnTwo.torusBaseOf Y n = (Y × S^{2n+1}) × S¹` of `CharClass/CohomologyKunnethTorusOf.lean`, whose
three projections carry no coefficients.

The statements are mod 2 and use the `F₂` Künneth layer (`KnHemi.kunneth_decomposition`,
`KnHemi.kunnethSecondInjective`), not the field-generic `…Of` twins at `K = ZMod 2`: the consumers
speak `Hmod2`, `TotalH`, `Wu.tClass` and `Gen.sphereClass`, and the `F₂` lemmas are stated over
exactly those objects, so no coefficient instance is ever compared.

## Main declarations

* `KnTwo.sig1N`, `KnTwo.sigOddN` — the two sphere classes on the model, mod 2.
* `KnTwo.tx_inj_degreeN` — the degreewise Künneth uniqueness for `z = t x`, in the shape of the
  hypothesis of `Gen.tx_inj_of_degreewise`; `KnTwo.tx_injN` — the ring-level field.
* `KnTwo.decomp_evenN`, `KnTwo.decomp_even_lowN` — the two-term decomposition in even degree.
* `KnTwo.totalSplitN` — **every even class of the model splits in the ring**, with the second
  coefficient in degree `d − (2n + 2)` and vanishing below `2n + 2`.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace KnTwo

variable (Y : Type) [TopologicalSpace Y] (n : ℕ)

/-! ## 1. The two sphere classes -/

/-- The degree-one class `t` on the rank-`n` model, mod 2. -/
def sig1N : Hmod2 (TopCat.of (torusBaseOf Y n)) 1 := knSigma (midBaseOf Y n) 1 (by omega)

/-- The degree-`(2n+1)` class `x` on the rank-`n` model, mod 2. -/
def sigOddN : Hmod2 (TopCat.of (torusBaseOf Y n)) (2 * n + 1) :=
  pull (knPrY (midBaseOf Y n) 1) (2 * n + 1) (knSigma Y (2 * n + 1) (by omega))

theorem sig1N_eq : sig1N Y n = knSigma (midBaseOf Y n) 1 (by omega) := rfl

theorem pull_prS1Of_sphereTopClass :
    pull (prS1Of Y n) 1 (sphereTopClass 1 (by omega)) = sig1N Y n := rfl

theorem pull_prSoddOf_sphereTopClass :
    pull (prSoddOf Y n) (2 * n + 1) (sphereTopClass (2 * n + 1) (by omega)) = sigOddN Y n := by
  rw [prSoddOf, pull_comp]
  rfl

theorem pull_prYOf_comp (k : ℕ) (c : Hmod2 (TopCat.of Y) k) :
    pull (knPrY (midBaseOf Y n) 1) k (pull (knPrY Y (2 * n + 1)) k c) = pull (prYOf Y n) k c := by
  rw [prYOf, pull_comp]

theorem cup_sigOddN_pull (c : ℕ) (b : Hmod2 (TopCat.of Y) c) :
    cup (sigOddN Y n) (pull (prYOf Y n) c b)
      = pull (knPrY (midBaseOf Y n) 1) ((2 * n + 1) + c)
          (cup (knSigma Y (2 * n + 1) (by omega)) (pull (knPrY Y (2 * n + 1)) c b)) := by
  rw [pull_cup, sigOddN, prYOf, pull_comp]

/-! ## 2. Künneth uniqueness for `z = t x` -/

set_option maxHeartbeats 1000000 in
/-- **Künneth uniqueness for `z = t x` at rank `n`, in a single degree, mod 2.**  If
`pr_Y^* uu + t ⌣ (x ⌣ pr_Y^* vv) = 0` on `(Y × S^{2n+1}) × S¹` then `vv = 0`.  Stated in the
right-nested, cast-free shape of the hypothesis of `Gen.tx_inj_of_degreewise`. -/
theorem tx_inj_degreeN (c : ℕ) (uu : Hmod2 (TopCat.of Y) (1 + ((2 * n + 1) + c)))
    (vv : Hmod2 (TopCat.of Y) c)
    (h : pull (prYOf Y n) (1 + ((2 * n + 1) + c)) uu
      + cup (pull (prS1Of Y n) 1 (sphereTopClass 1 (by omega)))
          (cup (pull (prSoddOf Y n) (2 * n + 1) (sphereTopClass (2 * n + 1) (by omega)))
            (pull (prYOf Y n) c vv)) = 0) :
    vv = 0 := by
  rw [pull_prS1Of_sphereTopClass, pull_prSoddOf_sphereTopClass] at h
  have hslice : ∀ (k : ℕ) (a : Hmod2 (TopCat.of Y) k),
      pull (knSlice (midBaseOf Y n) 1 (northPole 0)) k (pull (prYOf Y n) k a)
        = pull (knPrY Y (2 * n + 1)) k a := by
    intro k a
    rw [prYOf, pull_comp, pull_knSlice_knPrY]
  have hsig1 : pull (knSlice (midBaseOf Y n) 1 (northPole 0)) 1 (sig1N Y n) = 0 :=
    pull_knSlice_knSigma (midBaseOf Y n) 1 (by omega) (northPole 0)
  -- the circle slice kills the `t x` term, so the first summand vanishes
  have hU : pull (knPrY Y (2 * n + 1)) (1 + ((2 * n + 1) + c)) uu = 0 := by
    have hh := congrArg (pull (knSlice (midBaseOf Y n) 1 (northPole 0))
      (1 + ((2 * n + 1) + c))) h
    rw [pull_add, pull_zero, hslice, pull_cup, hsig1, zero_cup, add_zero] at hh
    exact hh
  have h2 : cup (sig1N Y n) (cup (sigOddN Y n) (pull (prYOf Y n) c vv)) = 0 := by
    have hz : pull (prYOf Y n) (1 + ((2 * n + 1) + c)) uu = 0 := by
      rw [prYOf, pull_comp, hU, pull_zero]
    rwa [hz, zero_add] at h
  -- peel the circle factor, then the odd sphere
  have h5 : cup (knSigma Y (2 * n + 1) (by omega)) (pull (knPrY Y (2 * n + 1)) c vv) = 0 := by
    refine KnHemi.kunnethSecondInjective (midBaseOf Y n) 1 (by omega) ((2 * n + 1) + c) _ ?_
    rw [← cup_sigOddN_pull]
    exact h2
  exact KnHemi.kunnethSecondInjective Y (2 * n + 1) (by omega) c vv h5

/-- **The field `tx_inj` on the rank-`n` model, mod 2.**  The ring-level reading of
`tx_inj_degreeN`. -/
theorem tx_injN :
    ∀ u v : TotalH (TopCat.of Y),
      TotalH.map (prYOf Y n) u
          + Wu.tClass (prS1Of Y n) (sphereTopClass 1 (by omega))
            * Gen.sphereClass (prSoddOf Y n) (sphereTopClass (2 * n + 1) (by omega))
            * TotalH.map (prYOf Y n) v = 0 → v = 0 :=
  Gen.tx_inj_of_degreewise n (prYOf Y n) (prS1Of Y n) (prSoddOf Y n) _ _
    (fun c α β h => tx_inj_degreeN Y n c α β h)

/-! ## 3. The two-term decomposition in even degree -/

set_option maxHeartbeats 1000000 in
/-- **The two-term decomposition in even degree at rank `n`, mod 2.**  With no odd cohomology on
`Y`, a class of degree `1 + ((2n+1) + c)` with `c` even is a pullback from `Y` plus
`t ⌣ (x ⌣ pr_Y^* b)`: the `t`- and `x`-coordinates live in the odd degrees `(2n+1) + c` and
`1 + c` of `Y`. -/
theorem decomp_evenN (hodd : KnHemi.NoOddCohomology Y) (c : ℕ) (hc : Even c)
    (z : Hmod2 (TopCat.of (torusBaseOf Y n)) (1 + ((2 * n + 1) + c))) :
    ∃ (a : Hmod2 (TopCat.of Y) (1 + ((2 * n + 1) + c))) (b : Hmod2 (TopCat.of Y) c),
      z = pull (prYOf Y n) (1 + ((2 * n + 1) + c)) a
        + cup (sig1N Y n) (cup (sigOddN Y n) (pull (prYOf Y n) c b)) := by
  obtain ⟨r, hr⟩ := hc
  obtain ⟨A, B, hAB⟩ := KnHemi.kunneth_decomposition (midBaseOf Y n) 1 (by omega)
    (1 + ((2 * n + 1) + c)) ((2 * n + 1) + c) rfl z
  obtain ⟨a, a₅, hA⟩ := KnHemi.kunneth_decomposition Y (2 * n + 1) (by omega)
    (1 + ((2 * n + 1) + c)) (1 + c) (by omega) A
  obtain ⟨a₁, b, hB⟩ := KnHemi.kunneth_decomposition Y (2 * n + 1) (by omega)
    ((2 * n + 1) + c) c rfl B
  have h5 : a₅ = 0 := KnHemi.eq_zero_of_noOdd hodd ⟨r, by omega⟩ a₅
  have h1 : a₁ = 0 := KnHemi.eq_zero_of_noOdd hodd ⟨n + r, by omega⟩ a₁
  refine ⟨a, b, ?_⟩
  rw [hAB, hA, hB, h5, h1]
  simp only [pull_zero, cup_zero, cohCast_zero, add_zero, zero_add, cohCast_self]
  rw [pull_prYOf_comp, ← cup_sigOddN_pull, sig1N_eq]

set_option maxHeartbeats 1000000 in
/-- **Below degree `2n + 2` an even class is simply a pullback**, mod 2: there is no `t x` part,
and the `t`-coordinate has odd degree. -/
theorem decomp_even_lowN (hodd : KnHemi.NoOddCohomology Y) (k : ℕ) (hk : Even k)
    (hlt : k < 2 * n + 2) (z : Hmod2 (TopCat.of (torusBaseOf Y n)) k) :
    ∃ a : Hmod2 (TopCat.of Y) k, z = pull (prYOf Y n) k a := by
  obtain ⟨r, hr⟩ := hk
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · obtain ⟨A, hA⟩ := KnHemi.kunneth_low (midBaseOf Y n) 1 0 (by omega) z
    obtain ⟨a, ha⟩ := KnHemi.kunneth_low Y (2 * n + 1) 0 (by omega) A
    exact ⟨a, by rw [hA, ha, pull_prYOf_comp]⟩
  · obtain ⟨j, hj⟩ : ∃ j, 1 + j = k := ⟨k - 1, by omega⟩
    obtain ⟨A, B, hAB⟩ := KnHemi.kunneth_decomposition (midBaseOf Y n) 1 (by omega) k j hj z
    obtain ⟨a, ha⟩ := KnHemi.kunneth_low Y (2 * n + 1) k (by omega) A
    obtain ⟨a₁, ha₁⟩ := KnHemi.kunneth_low Y (2 * n + 1) j (by omega) B
    have h1 : a₁ = 0 := KnHemi.eq_zero_of_noOdd hodd ⟨r - 1, by omega⟩ a₁
    refine ⟨a, ?_⟩
    rw [hAB, ha, ha₁, h1]
    simp only [pull_zero, cup_zero, cohCast_zero, add_zero]
    rw [pull_prYOf_comp]

/-! ## 4. The split in the ring -/

set_option maxHeartbeats 1000000 in
/-- **Every even class of the rank-`n` model splits in the ring**, mod 2.  With no odd
cohomology on `Y`, a class `z` of even degree `d` is `pr_Y^* α + t x pr_Y^* β` in `TotalH`, with
`β` of degree `d − (2n + 2)` and `β = 0` when `d < 2n + 2`.  This is the shape of the field
`gamma_eq` of `Gen.WuStepDData`, degree by degree. -/
theorem totalSplitN (hodd : KnHemi.NoOddCohomology Y) (d : ℕ) (hd : Even d)
    (z : Hmod2 (TopCat.of (torusBaseOf Y n)) d) :
    ∃ (α : Hmod2 (TopCat.of Y) d) (β : Hmod2 (TopCat.of Y) (d - (2 * n + 2))),
      (d < 2 * n + 2 → β = 0) ∧
      TotalH.of (TopCat.of (torusBaseOf Y n)) d z
        = TotalH.map (prYOf Y n) (TotalH.of (TopCat.of Y) d α)
          + Wu.tClass (prS1Of Y n) (sphereTopClass 1 (by omega))
            * Gen.sphereClass (prSoddOf Y n) (sphereTopClass (2 * n + 1) (by omega))
            * TotalH.map (prYOf Y n) (TotalH.of (TopCat.of Y) (d - (2 * n + 2)) β) := by
  rcases Nat.lt_or_ge d (2 * n + 2) with hlt | hge
  · obtain ⟨a, ha⟩ := decomp_even_lowN Y n hodd d hd hlt z
    refine ⟨a, 0, fun _ => rfl, ?_⟩
    rw [ha, map_zero, map_zero, mul_zero, add_zero, TotalH.map_of]
  · obtain ⟨r, hr⟩ := hd
    have hc : Even (d - (2 * n + 2)) := ⟨r - (n + 1), by omega⟩
    have hdeg : 1 + ((2 * n + 1) + (d - (2 * n + 2))) = d := by omega
    obtain ⟨a, b, hab⟩ := decomp_evenN Y n hodd (d - (2 * n + 2)) hc (cohCast hdeg.symm z)
    refine ⟨cohCast hdeg a, b, fun h => absurd h (by omega), ?_⟩
    have hz : TotalH.of (TopCat.of (torusBaseOf Y n)) d z
        = TotalH.of (TopCat.of (torusBaseOf Y n)) (1 + ((2 * n + 1) + (d - (2 * n + 2))))
            (cohCast hdeg.symm z) :=
      (totalH_of_cohCast hdeg.symm z).symm
    rw [hz, hab, map_add, totalH_of_cohCast, TotalH.map_of, mul_assoc, Wu.tClass_eq_of,
      Gen.sphereClass_eq_of, TotalH.map_of, TotalH.of_mul, TotalH.of_mul,
      pull_prS1Of_sphereTopClass, pull_prSoddOf_sphereTopClass]

end KnTwo

end

/-! Audited on every build. -/

#audit_axioms KnTwo.tx_inj_degreeN
#audit_axioms KnTwo.tx_injN
#audit_axioms KnTwo.decomp_evenN
#audit_axioms KnTwo.decomp_even_lowN
#audit_axioms KnTwo.totalSplitN

end GroupApproximation.CharClass
