import GroupApproximation.CharClass.CohomologyKunnethLixN
import GroupApproximation.CharClass.CohomologyChartCoverOf
import GroupApproximation.CharClass.CohomologyProductBase
import GroupApproximation.CharClass.CohomologyKunnethParityOf
import GroupApproximation.CharClass.CohomologyKunnethSphereOf
import GroupApproximation.CharClass.KroneckerContractible
import GroupApproximation.CharClass.CohomologyKunnethSplitOf
import GroupApproximation.CharClass.ChernSplittingOfInjective
import GroupApproximation.CharClass.CupOneTotal
import GroupApproximation.CharClass.LIXStepDGenReal
import GroupApproximation.Meta.AxiomGuard

/-!
# The Künneth objects of the rank-`n` LIX base over a field

Lane `lx-kunneth` of the STW Problem LIX strengthening (`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`
§1.4–1.5).  Step D mod `p` asks, of the Chern classes of a bundle over the mapping-torus base
`N = S¹ × S^{2n+1} × Y`, `Y = ∏ⱼ ℂP^{dⱼ}`, that each splits as `pr_Y^* a + z pr_Y^* b` with
`z = t x` and `b` in the right degree (the fields `γ_eq`, `b_low`, `b_deg` of
`Gen.RealBundleModP`).  This file is `CharClass/CohomologyKunnethLixN.lean` over a field `K`, at the
same three projections `KnLix.prY`, `KnLix.prS1`, `KnLix.prSodd` — only the cohomology changes,
never the maps — and at the fundamental classes `sphereTopClassOf K 1 _`,
`sphereTopClassOf K (2n+1) _`.

Three things are new over `K`.

* **No odd cohomology on `Y`.**  At `F₂` it is `KnCP.noOddCohomology_piCP`.  Over `K` the same
  induction runs on the field-generic chart cover of `U × ℂP^{d+1}` (`CohomologyChartCoverOf`): in odd
  degree both pieces vanish, so a class is a connecting-map image from the intersection
  `U × S^{2d+1}` in even degree, where it is pulled back from `U` and killed by the connecting map.
* **The split at the fundamental classes.**  `KnHemi.kunneth_decompositionOf` is stated at
  `knSigmaOf`, which **is** the pulled-back fundamental class, so no rescaling enters.
* **A slice.**  `KnLix.slice n dd p₁ q : y ↦ (p₁, (q, y))` is a section of `KnLix.prY` whose
  composite with `KnLix.prS1` is constant, so pulling back along it recovers the `Y`-coordinate and
  kills `z`.

## Main declarations

* `KnCP.noOddCohomology_prod_CPOf`, `KnCP.noOddCohomology_piCPOf`, `KnCP.noOddCohomology_baseYOf`.
* `KnTwo.decomp_even_topOfK`, `KnTwo.decomp_even_lowOfK`, `KnTwo.totalSplitOfK` — on the model.
* `KnLix.evenKunnethSplitOf` — **every even class of `KGen.lixN n dd` splits over `K`**, in the shape
  of `Gen.EvenKunnethSplitOf` (lane `lx-bundleP`).
* `KnLix.slice`, `KnLix.slice_comp_prY`, `KnLix.slice_comp_prS1`, `KnLix.slice_map_prY_map`,
  `KnLix.slice_map_zClass`.
-/

open CategoryTheory Limits TopologicalSpace
open scoped Matrix
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.CharClass.CPn

namespace GroupApproximation.CharClass

noncomputable section

/-! ## 1. No odd cohomology on the base, over a field -/

namespace KnCP

variable (K : Type) [Field K]

set_option maxHeartbeats 1000000 in
/-- **The induction step over `K`.**  If `U` and `U × ℂP^d` have no odd `K`-cohomology, neither
does `U × ℂP^{d+1}`. -/
theorem eq_zero_odd_prod_CP_succOf (U : Type) [TopologicalSpace U] (d : ℕ)
    (hU : KnHemi.NoOddCohomologyOf K U) (hP : KnHemi.NoOddCohomologyOf K (U × CP d))
    (k : ℕ) (hk : Odd k) (z : Hmod K (cpProdTop U d) k) : z = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by rw [Nat.odd_iff] at hk; omega⟩
  have hzU : (mvResUOf K (chartU U d) (punctU U d) (cp_sup U d) (j + 1)).hom z = 0 := by
    have h := isZero_of_linearEquivOf
      (pullEquivOfHomotopyEquivOf K (chartHomotopyEquiv U d) (j + 1)) (hU (j + 1) hk)
    rw [ModuleCat.isZero_iff_subsingleton] at h
    exact h.elim _ _
  have hzV : (mvResVOf K (chartU U d) (punctU U d) (cp_sup U d) (j + 1)).hom z = 0 := by
    have h := isZero_of_linearEquivOf
      (pullEquivOfHomotopyEquivOf K (punctHomotopyEquiv U d) (j + 1)) (hP (j + 1) hk)
    rw [ModuleCat.isZero_iff_subsingleton] at h
    exact h.elim _ _
  obtain ⟨w, hw⟩ := (mvExactXOf K (chartU U d) (punctU U d) (cp_sup U d) j z).1 ⟨hzU, hzV⟩
  obtain ⟨w', hw'⟩ : ∃ w', pull (cmap (interHomotopyEquiv U d).toFun) j w' = w :=
    ⟨(interPullEquivOf K U d j).symm w, (interPullEquivOf K U d j).apply_symm_apply w⟩
  obtain ⟨c, hc⟩ := KnHemi.even_pulled_back_of_odd_sphereOf K U (2 * d + 1) (by omega) hU
    (by rw [Nat.odd_iff]; omega) j (by rw [Nat.even_iff]; rw [Nat.odd_iff] at hk; omega) w'
  rw [← hw, ← hw', hc, pull_interHE_prUOf, mvDeltaOf_pull_cpPrSub_inter]

/-- **A projective factor preserves the absence of odd cohomology**, over a field. -/
theorem noOddCohomology_prod_CPOf (U : Type) [TopologicalSpace U]
    (hU : KnHemi.NoOddCohomologyOf K U) :
    ∀ d : ℕ, KnHemi.NoOddCohomologyOf K (U × CP d) := by
  intro d
  induction d with
  | zero =>
    intro j hj
    exact isZero_of_linearEquivOf (cohProdContractibleOf K U (CP 0) j) (hU j hj)
  | succ e ih =>
    intro j hj
    rw [ModuleCat.isZero_iff_subsingleton]
    refine ⟨fun z w => ?_⟩
    rw [eq_zero_odd_prod_CP_succOf K U e hU ih j hj z,
      eq_zero_odd_prod_CP_succOf K U e hU ih j hj w]

/-- The absence of odd cohomology transports along a homeomorphism, over any field. -/
theorem noOddCohomologyOf_of_homeomorph {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) (hB : KnHemi.NoOddCohomologyOf K B) : KnHemi.NoOddCohomologyOf K A :=
  fun j hj => isZero_of_linearEquivOf (pullEquivOfHomotopyEquivOf K e.toHomotopyEquiv j) (hB j hj)

/-- **A dependent product of projective spaces has no odd cohomology**, over a field. -/
theorem noOddCohomology_piCPOf :
    ∀ (ℓ : ℕ) (dd : Fin ℓ → ℕ), KnHemi.NoOddCohomologyOf K (∀ j : Fin ℓ, CP (dd j)) := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro dd
    refine noOddCohomologyOf_of_homeomorph K
      (Homeomorph.homeomorphOfUnique (∀ j : Fin 0, CP (dd j)) Unit) ?_
    intro j hj
    exact cohomology_unit_isZeroOf K j (by rw [Nat.odd_iff] at hj; omega)
  | succ e ih =>
    intro dd
    exact noOddCohomologyOf_of_homeomorph K (baseYSnocHomeo e dd)
      (noOddCohomology_prod_CPOf K _ (ih fun i => dd i.castSucc) (dd (Fin.last e)))

/-- The program's base has no odd cohomology over any field. -/
theorem noOddCohomology_baseYOf {ℓ : ℕ} (dd : Fin ℓ → ℕ) :
    KnHemi.NoOddCohomologyOf K (baseY dd) :=
  noOddCohomology_piCPOf K ℓ dd

end KnCP

/-! ## 2. The split on the model, over a field -/

namespace KnTwo

variable (K : Type) [Field K] (Y : Type) [TopologicalSpace Y] (n : ℕ)

theorem pull_prYOf_compK (k : ℕ) (c : Hmod K (TopCat.of Y) k) :
    pull (knPrY (midBaseOf Y n) 1) k (pull (knPrY Y (2 * n + 1)) k c) = pull (prYOf Y n) k c := by
  rw [prYOf, pull_comp]

theorem knSigmaOf_midBaseOf :
    knSigmaOf K (midBaseOf Y n) 1 (by omega)
      = pull (prS1Of Y n) 1 (sphereTopClassOf K 1 (by omega)) := rfl

theorem cup_pull_prSoddOfK (c : ℕ) (b : Hmod K (TopCat.of Y) c) :
    cup (pull (prSoddOf Y n) (2 * n + 1) (sphereTopClassOf K (2 * n + 1) (by omega)))
        (pull (prYOf Y n) c b)
      = pull (knPrY (midBaseOf Y n) 1) ((2 * n + 1) + c)
          (cup (knSigmaOf K Y (2 * n + 1) (by omega)) (pull (knPrY Y (2 * n + 1)) c b)) := by
  rw [pull_cup, knSigmaOf, prSoddOf, prYOf, pull_comp, pull_comp]

set_option maxHeartbeats 1000000 in
/-- **The two-term decomposition in even degree at rank `n`, over a field**, at the fundamental
classes of the two spheres. -/
theorem decomp_even_topOfK (hodd : KnHemi.NoOddCohomologyOf K Y) (c : ℕ) (hc : Even c)
    (z : Hmod K (TopCat.of (torusBaseOf Y n)) (1 + ((2 * n + 1) + c))) :
    ∃ (a : Hmod K (TopCat.of Y) (1 + ((2 * n + 1) + c))) (b : Hmod K (TopCat.of Y) c),
      z = pull (prYOf Y n) (1 + ((2 * n + 1) + c)) a
        + cup (pull (prS1Of Y n) 1 (sphereTopClassOf K 1 (by omega)))
            (cup (pull (prSoddOf Y n) (2 * n + 1) (sphereTopClassOf K (2 * n + 1) (by omega)))
              (pull (prYOf Y n) c b)) := by
  obtain ⟨r, hr⟩ := hc
  obtain ⟨A, B, hAB⟩ := KnHemi.kunneth_decompositionOf K (midBaseOf Y n) 1 (by omega)
    (1 + ((2 * n + 1) + c)) ((2 * n + 1) + c) rfl z
  obtain ⟨a, a₅, hA⟩ := KnHemi.kunneth_decompositionOf K Y (2 * n + 1) (by omega)
    (1 + ((2 * n + 1) + c)) (1 + c) (by omega) A
  obtain ⟨a₁, b, hB⟩ := KnHemi.kunneth_decompositionOf K Y (2 * n + 1) (by omega)
    ((2 * n + 1) + c) c rfl B
  have h5 : a₅ = 0 := KnHemi.eq_zero_of_noOddOf hodd ⟨r, by omega⟩ a₅
  have h1 : a₁ = 0 := KnHemi.eq_zero_of_noOddOf hodd ⟨n + r, by omega⟩ a₁
  refine ⟨a, b, ?_⟩
  rw [hAB, hA, hB, h5, h1]
  simp only [pull_zero, cup_zero, CharClass.cohCast_zero, add_zero, zero_add, cohCast_self]
  rw [pull_prYOf_compK, cup_pull_prSoddOfK, knSigmaOf_midBaseOf]

set_option maxHeartbeats 1000000 in
/-- **Below degree `2n + 2` an even class is a pullback**, over a field. -/
theorem decomp_even_lowOfK (hodd : KnHemi.NoOddCohomologyOf K Y) (k : ℕ) (hk : Even k)
    (hlt : k < 2 * n + 2) (z : Hmod K (TopCat.of (torusBaseOf Y n)) k) :
    ∃ a : Hmod K (TopCat.of Y) k, z = pull (prYOf Y n) k a := by
  obtain ⟨r, hr⟩ := hk
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · obtain ⟨A, hA⟩ := KnHemi.kunneth_lowOf K (midBaseOf Y n) 1 0 (by omega) z
    obtain ⟨a, ha⟩ := KnHemi.kunneth_lowOf K Y (2 * n + 1) 0 (by omega) A
    exact ⟨a, by rw [hA, ha, pull_prYOf_compK]⟩
  · obtain ⟨j, hj⟩ : ∃ j, 1 + j = k := ⟨k - 1, by omega⟩
    obtain ⟨A, B, hAB⟩ := KnHemi.kunneth_decompositionOf K (midBaseOf Y n) 1 (by omega) k j hj z
    obtain ⟨a, ha⟩ := KnHemi.kunneth_lowOf K Y (2 * n + 1) k (by omega) A
    obtain ⟨a₁, ha₁⟩ := KnHemi.kunneth_lowOf K Y (2 * n + 1) j (by omega) B
    have h1 : a₁ = 0 := KnHemi.eq_zero_of_noOddOf hodd ⟨r - 1, by omega⟩ a₁
    refine ⟨a, ?_⟩
    rw [hAB, ha, ha₁, h1]
    simp only [pull_zero, cup_zero, CharClass.cohCast_zero, add_zero]
    rw [pull_prYOf_compK]

set_option maxHeartbeats 1000000 in
/-- **Every even class of the model splits in the ring, over a field**, at the fundamental
classes: in degree `2k`, `z = pr_Y^* α + z_{t x} pr_Y^* β` with `β` in degree `2(k − (n+1))` and
`β = 0` for `k < n + 1`. -/
theorem totalSplitOfK (hodd : KnHemi.NoOddCohomologyOf K Y) (k : ℕ)
    (z : Hmod K (TopCat.of (torusBaseOf Y n)) (2 * k)) :
    ∃ (α : Hmod K (TopCat.of Y) (2 * k)) (β : Hmod K (TopCat.of Y) (2 * (k - (n + 1)))),
      (k < n + 1 → β = 0) ∧
      TotalHOf.of K (TopCat.of (torusBaseOf Y n)) (2 * k) z
        = TotalHOf.map K (prYOf Y n) (TotalHOf.of K (TopCat.of Y) (2 * k) α)
          + Gen.zClass K (prS1Of Y n) (prSoddOf Y n) (sphereTopClassOf K 1 (by omega))
              (sphereTopClassOf K (2 * n + 1) (by omega))
            * TotalHOf.map K (prYOf Y n) (TotalHOf.of K (TopCat.of Y) (2 * (k - (n + 1))) β) := by
  rcases Nat.lt_or_ge k (n + 1) with hlt | hge
  · obtain ⟨a, ha⟩ := decomp_even_lowOfK K Y n hodd (2 * k) ⟨k, by omega⟩ (by omega) z
    refine ⟨a, 0, fun _ => rfl, ?_⟩
    rw [ha, map_zero, map_zero, mul_zero, add_zero, TotalHOf.map_of]
  · have hc : Even (2 * (k - (n + 1))) := ⟨k - (n + 1), by omega⟩
    have hdeg : 1 + ((2 * n + 1) + 2 * (k - (n + 1))) = 2 * k := by omega
    obtain ⟨a, b, hab⟩ := decomp_even_topOfK K Y n hodd (2 * (k - (n + 1))) hc
      (cohCast hdeg.symm z)
    refine ⟨cohCast hdeg a, b, fun h => absurd h (by omega), ?_⟩
    have hz : TotalHOf.of K (TopCat.of (torusBaseOf Y n)) (2 * k) z
        = TotalHOf.of K (TopCat.of (torusBaseOf Y n)) (1 + ((2 * n + 1) + 2 * (k - (n + 1))))
            (cohCast hdeg.symm z) :=
      (TotalHOf.of_cohCast K _ hdeg.symm z).symm
    rw [hz, hab, map_add, TotalHOf.of_cohCast, TotalHOf.map_of, Gen.zClass, Gen.tClassOf,
      Gen.xClassOf, TotalHOf.map_of, TotalHOf.map_of, TotalHOf.map_of, mul_assoc,
      ← TotalHOf.of_mul, ← TotalHOf.of_mul]

end KnTwo

/-! ## 3. At the geometric base, over a field -/

namespace KnLix

variable {ℓ : ℕ} (K : Type) [Field K]

theorem map_hom_prYOfK (n : ℕ) (dd : Fin ℓ → ℕ) (w : TotalHOf K (TopCat.of (baseY dd))) :
    TotalHOf.map K (lixIso n dd).hom (TotalHOf.map K (KnTwo.prYOf (baseY dd) n) w)
      = TotalHOf.map K (prY n dd) w := by
  rw [← ChernSplittingOf.totalHOf_map_comp]
  rfl

theorem map_hom_zClassOfK (n : ℕ) (dd : Fin ℓ → ℕ)
    (σ₁ : TotalPieceOf K (TopCat.of (Sphere 1)) 1) {c : ℕ}
    (σodd : TotalPieceOf K (TopCat.of (Sphere (2 * n + 1))) c) :
    TotalHOf.map K (lixIso n dd).hom
        (Gen.zClass K (KnTwo.prS1Of (baseY dd) n) (KnTwo.prSoddOf (baseY dd) n) σ₁ σodd)
      = Gen.zClass K (prS1 n dd) (prSodd n dd) σ₁ σodd := by
  simp only [Gen.zClass, Gen.tClassOf, Gen.xClassOf, map_mul]
  rw [← ChernSplittingOf.totalHOf_map_comp, ← ChernSplittingOf.totalHOf_map_comp]
  rfl

set_option maxHeartbeats 1000000 in
/-- **Every even class of the rank-`n` base splits over a field.**  The statement is the body of
`Gen.EvenKunnethSplitOf n K (KnLix.prY n dd) (KnLix.prS1 n dd) (KnLix.prSodd n dd)
(sphereTopClassOf K 1 _) (sphereTopClassOf K (2n+1) _)` verbatim (lane `lx-bundleP`). -/
theorem evenKunnethSplitOf (n : ℕ) (dd : Fin ℓ → ℕ) :
    ∀ (k : ℕ) (x : TotalPieceOf K (KGen.lixN n dd) (2 * k)),
      ∃ (α : TotalPieceOf K (TopCat.of (baseY dd)) (2 * k))
        (β : TotalPieceOf K (TopCat.of (baseY dd)) (2 * (k - (n + 1)))),
        (k < n + 1 → β = 0) ∧
          TotalHOf.of K (KGen.lixN n dd) (2 * k) x
            = TotalHOf.map K (prY n dd) (TotalHOf.of K (TopCat.of (baseY dd)) (2 * k) α)
              + Gen.zClass K (prS1 n dd) (prSodd n dd) (sphereTopClassOf K 1 (by omega))
                  (sphereTopClassOf K (2 * n + 1) (by omega))
                * TotalHOf.map K (prY n dd)
                    (TotalHOf.of K (TopCat.of (baseY dd)) (2 * (k - (n + 1))) β) := by
  intro k x
  obtain ⟨α, β, hβ, hsplit⟩ := KnTwo.totalSplitOfK K (baseY dd) n
    (KnCP.noOddCohomology_baseYOf K dd) k (pull (lixIso n dd).inv (2 * k) x)
  refine ⟨α, β, hβ, ?_⟩
  have hk := congrArg (TotalHOf.map K (lixIso n dd).hom) hsplit
  rw [← TotalHOf.map_of, ← ChernSplittingOf.totalHOf_map_comp, (lixIso n dd).hom_inv_id,
    ChernSplittingOf.totalHOf_map_id, map_add, map_mul, map_hom_prYOfK, map_hom_prYOfK,
    map_hom_zClassOfK] at hk
  exact hk

/-! ## 4. The slice -/

/-- **The slice `y ↦ (p₁, (q, y))` of the rank-`n` base**, a section of `KnLix.prY` at a constant
circle point and a constant sphere point. -/
def slice (n : ℕ) (dd : Fin ℓ → ℕ) (p₁ : Sphere 1) (q : ↥(unitVectors (Fin (n + 1)))) :
    TopCat.of (baseY dd) ⟶ KGen.lixN n dd :=
  cmap ⟨fun y => (p₁, (q, y)), continuous_const.prodMk (continuous_const.prodMk continuous_id)⟩

theorem slice_comp_prY (n : ℕ) (dd : Fin ℓ → ℕ) (p₁ : Sphere 1) (q : ↥(unitVectors (Fin (n + 1)))) :
    slice n dd p₁ q ≫ prY n dd = 𝟙 (TopCat.of (baseY dd)) := rfl

theorem slice_comp_prS1 (n : ℕ) (dd : Fin ℓ → ℕ) (p₁ : Sphere 1)
    (q : ↥(unitVectors (Fin (n + 1)))) :
    slice n dd p₁ q ≫ prS1 n dd = cmap (ContinuousMap.const (baseY dd) p₁) := rfl

/-- **Pulling back along the slice recovers the `Y`-coordinate**, over any ring. -/
theorem slice_map_prY_map (n : ℕ) (dd : Fin ℓ → ℕ) (p₁ : Sphere 1)
    (q : ↥(unitVectors (Fin (n + 1)))) (c : TotalHOf K (TopCat.of (baseY dd))) :
    TotalHOf.map K (slice n dd p₁ q) (TotalHOf.map K (prY n dd) c) = c := by
  rw [← ChernSplittingOf.totalHOf_map_comp, slice_comp_prY, ChernSplittingOf.totalHOf_map_id]

/-- **The slice kills `z = t x`**: its composite with the circle projection is constant, and a
constant map kills `H¹`. -/
theorem slice_map_zClass (n : ℕ) (dd : Fin ℓ → ℕ) (p₁ : Sphere 1)
    (q : ↥(unitVectors (Fin (n + 1))))
    (σ₁ : TotalPieceOf K (TopCat.of (Sphere 1)) 1) {c : ℕ}
    (σodd : TotalPieceOf K (TopCat.of (Sphere (2 * n + 1))) c) :
    TotalHOf.map K (slice n dd p₁ q) (Gen.zClass K (prS1 n dd) (prSodd n dd) σ₁ σodd) = 0 := by
  rw [Gen.zClass, map_mul, Gen.tClassOf, ← ChernSplittingOf.totalHOf_map_comp, slice_comp_prS1,
    TotalHOf.map_of, pull_const_eq_zeroOf K (baseY dd) p₁ 1 le_rfl σ₁, map_zero, zero_mul]

end KnLix

end

/-! Audited on every build. -/

#audit_axioms KnCP.noOddCohomology_piCPOf
#audit_axioms KnTwo.totalSplitOfK
#audit_axioms KnLix.evenKunnethSplitOf
#audit_axioms KnLix.slice_map_prY_map
#audit_axioms KnLix.slice_map_zClass

end GroupApproximation.CharClass
