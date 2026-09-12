import GroupApproximation.KunThom.CentralizerNormalizationSumPoincare
import GroupApproximation.Matching.PartialSwapEquivariance

/-!
# Rounding a relation near a swap graph to a cluster candidate

Let `X` and `Z` carry labels `actX` and `actZ` with exact Cheeger bounds, let
`b : X ⇢ Z` be a partial bijection and let `U` be a relation on `X ⊕ Z` that
is close to the graph of the swap involution of `b` and has small diagonal
boundary.  Singleton-core rounding (`CentralizerNormalizationSumPoincare`)
gives a permutation `p` of `X ⊕ Z` whose commutation defect is controlled by
the boundary of `U`.  Its left-to-right crossing is a partial bijection close
to `b`.

The candidate conditions need more than closeness.  They ask that the
missing sources and targets of the crossing are small at the scale of the
equivariance defect, not at the scale of the distance to `b`.  The points of
`X` that `p` does not send across form an almost invariant set: every label arc
leaving it is a commutation failure of `p`.  Expansion of `X` bounds such a set
by the defect of `p` divided by the Cheeger constant
(`cheeger_mul_sourceDefect_extractCrossing_le`), and the same argument on `Z`
for `p⁻¹` bounds the missing targets.
-/

namespace GroupApproximation
namespace CentralizerNormalizationCrossingRepair

open AlmostAutomorphism
open KazhdanImprovement
open FinitePartialBijection
open CentralizerNormalizationFiberCoarea
open CentralizerNormalizationSumPoincare

variable {L : Type*} {X Z : FiniteModel}

@[simp] theorem sumAction_apply_inl [Fintype L] [DecidableEq L]
    (actX : L → Equiv.Perm X) (actZ : L → Equiv.Perm Z) (l : L) (x : X) :
    sumAction actX actZ l (Sum.inl x) = Sum.inl (actX l x) := rfl

@[simp] theorem sumAction_apply_inr [Fintype L] [DecidableEq L]
    (actX : L → Equiv.Perm X) (actZ : L → Equiv.Perm Z) (l : L) (z : Z) :
    sumAction actX actZ l (Sum.inr z) = Sum.inr (actZ l z) := rfl

theorem sumAction_eq_sumCongr_parts [Fintype L] [DecidableEq L]
    (actX : L → Equiv.Perm X) (actZ : L → Equiv.Perm Z) (l : L) :
    sumAction actX actZ l =
      Equiv.sumCongr (leftPart (sumAction actX actZ l))
        (rightPart (sumAction actX actZ l)) := by
  simp [sumAction]

/-- The labels of the union preserve both summands. -/
theorem image_sumAction_preserves [Fintype L] [DecidableEq L]
    (actX : L → Equiv.Perm X) (actZ : L → Equiv.Perm Z) :
    ∀ σ ∈ Finset.univ.image (sumAction actX actZ),
      σ = Equiv.sumCongr (leftPart σ) (rightPart σ) := by
  intro σ hσ
  obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hσ
  exact sumAction_eq_sumCongr_parts actX actZ l

open Classical in
theorem image_leftPart_image_sumAction [Fintype L] [DecidableEq L]
    (actX : L → Equiv.Perm X) (actZ : L → Equiv.Perm Z) :
    (Finset.univ.image (sumAction actX actZ)).image leftPart =
      Finset.univ.image actX := by
  rw [Finset.image_image]
  congr 1
  funext l
  simp [sumAction]

open Classical in
theorem image_rightPart_image_sumAction [Fintype L] [DecidableEq L]
    (actX : L → Equiv.Perm X) (actZ : L → Equiv.Perm Z) :
    (Finset.univ.image (sumAction actX actZ)).image rightPart =
      Finset.univ.image actZ := by
  rw [Finset.image_image]
  congr 1
  funext l
  simp [sumAction]

/-! ### Bad arcs of a permutation and tagged commutation failures -/

/-- Every untagged bad arc of `c` for the image labels comes from a tagged
commutation failure. -/
theorem card_badArcs_image_sumAction_le [Fintype L] [DecidableEq L]
    (actX : L → Equiv.Perm X) (actZ : L → Equiv.Perm Z)
    (c : Equiv.Perm (sumModel X Z)) :
    (badArcs (sumModel X Z) (Finset.univ.image (sumAction actX actZ)) c).card ≤
      (sumCommutationDefect c actX actZ).card := by
  classical
  refine (Finset.card_le_card
    (t := (sumCommutationDefect c actX actZ).image
      fun x : L × (X ⊕ Z) ↦ (sumAction actX actZ x.1, x.2)) ?_).trans
    Finset.card_image_le
  intro q hq
  rw [mem_badArcs] at hq
  obtain ⟨hq1, hbad⟩ := hq
  obtain ⟨l, -, hl⟩ := Finset.mem_image.mp hq1
  refine Finset.mem_image.mpr ⟨(l, q.2), ?_, ?_⟩
  · rw [mem_sumCommutationDefect]
    simpa only [hl] using hbad
  · simp [hl]

/-! ### Missing sources of a crossing are controlled by expansion -/

/-- A label arc on which the crossing property of `p` changes is a
commutation failure of `p`. -/
theorem mem_badArcs_of_crossingSource_boundary [Fintype L] [DecidableEq L]
    (actX : L → Equiv.Perm X) (actZ : L → Equiv.Perm Z)
    (p : Equiv.Perm (sumModel X Z)) (l : L) (x : X)
    (hbd : (x ∉ crossingSource p ∧ actX l x ∈ crossingSource p) ∨
      (x ∈ crossingSource p ∧ actX l x ∉ crossingSource p)) :
    p (sumAction actX actZ l (Sum.inl x)) ≠
      sumAction actX actZ l (p (Sum.inl x)) := by
  rw [sumAction_apply_inl]
  rcases hbd with ⟨hx, hax⟩ | ⟨hx, hax⟩
  · obtain ⟨z, hz⟩ := (mem_crossingSource p (actX l x)).mp hax
    rw [hz]
    intro h
    cases hpx : p (Sum.inl x) with
    | inl y =>
        rw [hpx, sumAction_apply_inl] at h
        exact Sum.inr_ne_inl h
    | inr z' =>
        exact hx ((mem_crossingSource p x).mpr ⟨z', hpx⟩)
  · obtain ⟨z, hz⟩ := (mem_crossingSource p x).mp hx
    rw [hz, sumAction_apply_inr]
    intro h
    cases hpax : p (Sum.inl (actX l x)) with
    | inl y =>
        rw [hpax] at h
        exact Sum.inl_ne_inr h
    | inr z' =>
        exact hax ((mem_crossingSource p (actX l x)).mpr ⟨z', hpax⟩)

open Classical in
/-- **Missing sources of the crossing.**  If at most half of `X` fails to
cross, the number of non-crossing points is at most the commutation defect of
`p` divided by the Cheeger constant of `X`. -/
theorem cheeger_mul_sourceDefect_extractCrossing_le [Fintype L] [DecidableEq L]
    (actX : L → Equiv.Perm X) (actZ : L → Equiv.Perm Z) {hc : ℝ}
    (hX : DirectedCoarea.HasCheegerLowerBound X (Finset.univ.image actX) hc)
    (p : Equiv.Perm (sumModel X Z))
    (hhalf : 2 * (extractCrossing p).sourceDefect ≤ Fintype.card X) :
    hc * ((extractCrossing p).sourceDefect : ℝ) ≤
      ((badArcs (sumModel X Z) (Finset.univ.image (sumAction actX actZ)) p).card :
        ℝ) := by
  classical
  have hcardA : ((crossingSource p)ᶜ).card = (extractCrossing p).sourceDefect := by
    rw [Finset.card_compl]
    rfl
  rcases ((crossingSource p)ᶜ).eq_empty_or_nonempty with hempty | hne
  · rw [← hcardA, hempty, Finset.card_empty, Nat.cast_zero, mul_zero]
    positivity
  · have hcheeger := hX.2 ((crossingSource p)ᶜ) hne (by rw [hcardA]; exact hhalf)
    have hcharge :
        (directedBoundary X (Finset.univ.image actX) ((crossingSource p)ᶜ)).card ≤
          (badArcs (sumModel X Z) (Finset.univ.image (sumAction actX actZ)) p).card := by
      let f : Arc X → Arc (sumModel X Z) := fun q ↦
        if h : ∃ l, actX l = q.1 then
          (sumAction actX actZ (Classical.choose h), Sum.inl q.2)
        else (1, Sum.inl q.2)
      refine Finset.card_le_card_of_injOn f ?_ ?_
      · intro q hq
        rw [Finset.mem_coe, mem_directedBoundary] at hq
        obtain ⟨hq1, hbd⟩ := hq
        have hex : ∃ l, actX l = q.1 := by
          obtain ⟨l, -, hl⟩ := Finset.mem_image.mp hq1
          exact ⟨l, hl⟩
        have hfq : f q =
            (sumAction actX actZ (Classical.choose hex), Sum.inl q.2) := by
          simp only [f, dif_pos hex]
        rw [Finset.mem_coe, hfq, mem_badArcs]
        refine ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
        apply mem_badArcs_of_crossingSource_boundary actX actZ p
          (Classical.choose hex) q.2
        rw [Classical.choose_spec hex]
        simpa only [Finset.mem_compl, not_not] using hbd
      · intro q₁ hq₁ q₂ hq₂ heq
        rw [Finset.mem_coe, mem_directedBoundary] at hq₁ hq₂
        have hex₁ : ∃ l, actX l = q₁.1 := by
          obtain ⟨l, -, hl⟩ := Finset.mem_image.mp hq₁.1
          exact ⟨l, hl⟩
        have hex₂ : ∃ l, actX l = q₂.1 := by
          obtain ⟨l, -, hl⟩ := Finset.mem_image.mp hq₂.1
          exact ⟨l, hl⟩
        simp only [f, dif_pos hex₁, dif_pos hex₂, Prod.mk.injEq] at heq
        obtain ⟨hσ, hx⟩ := heq
        have hact : actX (Classical.choose hex₁) = actX (Classical.choose hex₂) := by
          ext y
          have hy := congrArg
            (fun τ : Equiv.Perm (sumModel X Z) ↦ τ (Sum.inl y)) hσ
          simpa using hy
        refine Prod.ext ?_ (Sum.inl_injective hx)
        calc q₁.1 = actX (Classical.choose hex₁) := (Classical.choose_spec hex₁).symm
          _ = actX (Classical.choose hex₂) := hact
          _ = q₂.1 := Classical.choose_spec hex₂
    have hcast :
        ((directedBoundary X (Finset.univ.image actX) ((crossingSource p)ᶜ)).card : ℝ) ≤
          ((badArcs (sumModel X Z) (Finset.univ.image (sumAction actX actZ)) p).card :
            ℝ) := by
      exact_mod_cast hcharge
    rw [← hcardA]
    exact hcheeger.trans hcast

/-! ### Missing targets of a crossing -/

theorem inv_apply_inr_of_mem_crossingTarget (p : Equiv.Perm (sumModel X Z)) (z : Z)
    (hz : z ∈ crossingTarget p) : ∃ y : X, p⁻¹ (Sum.inr z) = Sum.inl y := by
  obtain ⟨y, hy⟩ := (mem_crossingTarget p z).mp hz
  refine ⟨y, ?_⟩
  rw [← hy]
  exact Equiv.symm_apply_apply p (Sum.inl y)

theorem inv_apply_inr_of_not_mem_crossingTarget (p : Equiv.Perm (sumModel X Z))
    (z : Z) (hz : z ∉ crossingTarget p) : ∃ w : Z, p⁻¹ (Sum.inr z) = Sum.inr w := by
  cases hw : p⁻¹ (Sum.inr z) with
  | inl y =>
      exfalso
      apply hz
      rw [mem_crossingTarget]
      refine ⟨y, ?_⟩
      rw [← hw]
      exact Equiv.apply_symm_apply p (Sum.inr z)
  | inr w => exact ⟨w, rfl⟩

/-- A label arc on which the crossing-target property changes is a
commutation failure of `p⁻¹`. -/
theorem mem_badArcs_inv_of_crossingTarget_boundary [Fintype L] [DecidableEq L]
    (actX : L → Equiv.Perm X) (actZ : L → Equiv.Perm Z)
    (p : Equiv.Perm (sumModel X Z)) (l : L) (z : Z)
    (hbd : (z ∉ crossingTarget p ∧ actZ l z ∈ crossingTarget p) ∨
      (z ∈ crossingTarget p ∧ actZ l z ∉ crossingTarget p)) :
    p⁻¹ (sumAction actX actZ l (Sum.inr z)) ≠
      sumAction actX actZ l (p⁻¹ (Sum.inr z)) := by
  rw [sumAction_apply_inr]
  rcases hbd with ⟨hz, haz⟩ | ⟨hz, haz⟩
  · obtain ⟨w, hw⟩ := inv_apply_inr_of_not_mem_crossingTarget p z hz
    obtain ⟨y, hy⟩ := inv_apply_inr_of_mem_crossingTarget p (actZ l z) haz
    rw [hy, hw, sumAction_apply_inr]
    exact Sum.inl_ne_inr
  · obtain ⟨y, hy⟩ := inv_apply_inr_of_mem_crossingTarget p z hz
    obtain ⟨w, hw⟩ := inv_apply_inr_of_not_mem_crossingTarget p (actZ l z) haz
    rw [hw, hy, sumAction_apply_inl]
    exact Sum.inr_ne_inl

open Classical in
/-- **Missing targets of the crossing.** -/
theorem cheeger_mul_targetDefect_extractCrossing_le [Fintype L] [DecidableEq L]
    (actX : L → Equiv.Perm X) (actZ : L → Equiv.Perm Z) {hc : ℝ}
    (hZ : DirectedCoarea.HasCheegerLowerBound Z (Finset.univ.image actZ) hc)
    (p : Equiv.Perm (sumModel X Z))
    (hhalf : 2 * (extractCrossing p).targetDefect ≤ Fintype.card Z) :
    hc * ((extractCrossing p).targetDefect : ℝ) ≤
      ((badArcs (sumModel X Z) (Finset.univ.image (sumAction actX actZ)) p).card :
        ℝ) := by
  classical
  have hcardB : ((crossingTarget p)ᶜ).card = (extractCrossing p).targetDefect := by
    rw [Finset.card_compl]
    rfl
  rcases ((crossingTarget p)ᶜ).eq_empty_or_nonempty with hempty | hne
  · rw [← hcardB, hempty, Finset.card_empty, Nat.cast_zero, mul_zero]
    positivity
  · have hcheeger := hZ.2 ((crossingTarget p)ᶜ) hne (by rw [hcardB]; exact hhalf)
    have hcharge :
        (directedBoundary Z (Finset.univ.image actZ) ((crossingTarget p)ᶜ)).card ≤
          (badArcs (sumModel X Z) (Finset.univ.image (sumAction actX actZ)) p⁻¹).card := by
      let f : Arc Z → Arc (sumModel X Z) := fun q ↦
        if h : ∃ l, actZ l = q.1 then
          (sumAction actX actZ (Classical.choose h), Sum.inr q.2)
        else (1, Sum.inr q.2)
      refine Finset.card_le_card_of_injOn f ?_ ?_
      · intro q hq
        rw [Finset.mem_coe, mem_directedBoundary] at hq
        obtain ⟨hq1, hbd⟩ := hq
        have hex : ∃ l, actZ l = q.1 := by
          obtain ⟨l, -, hl⟩ := Finset.mem_image.mp hq1
          exact ⟨l, hl⟩
        have hfq : f q =
            (sumAction actX actZ (Classical.choose hex), Sum.inr q.2) := by
          simp only [f, dif_pos hex]
        rw [Finset.mem_coe, hfq, mem_badArcs]
        refine ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
        apply mem_badArcs_inv_of_crossingTarget_boundary actX actZ p
          (Classical.choose hex) q.2
        rw [Classical.choose_spec hex]
        simpa only [Finset.mem_compl, not_not] using hbd
      · intro q₁ hq₁ q₂ hq₂ heq
        rw [Finset.mem_coe, mem_directedBoundary] at hq₁ hq₂
        have hex₁ : ∃ l, actZ l = q₁.1 := by
          obtain ⟨l, -, hl⟩ := Finset.mem_image.mp hq₁.1
          exact ⟨l, hl⟩
        have hex₂ : ∃ l, actZ l = q₂.1 := by
          obtain ⟨l, -, hl⟩ := Finset.mem_image.mp hq₂.1
          exact ⟨l, hl⟩
        simp only [f, dif_pos hex₁, dif_pos hex₂, Prod.mk.injEq] at heq
        obtain ⟨hσ, hz⟩ := heq
        have hact : actZ (Classical.choose hex₁) = actZ (Classical.choose hex₂) := by
          ext w
          have hw := congrArg
            (fun τ : Equiv.Perm (sumModel X Z) ↦ τ (Sum.inr w)) hσ
          simpa using hw
        refine Prod.ext ?_ (Sum.inr_injective hz)
        calc q₁.1 = actZ (Classical.choose hex₁) := (Classical.choose_spec hex₁).symm
          _ = actZ (Classical.choose hex₂) := hact
          _ = q₂.1 := Classical.choose_spec hex₂
    have hcast :
        ((directedBoundary Z (Finset.univ.image actZ) ((crossingTarget p)ᶜ)).card : ℝ) ≤
          ((badArcs (sumModel X Z) (Finset.univ.image (sumAction actX actZ)) p).card :
            ℝ) := by
      rw [← card_badArcs_inv]
      exact_mod_cast hcharge
    rw [← hcardB]
    exact hcheeger.trans hcast

/-! ### The finite repair step -/

theorem card_hammingDisagreement_comm {Y : FiniteModel} (p q : Equiv.Perm Y) :
    (hammingDisagreement p q).card = (hammingDisagreement q p).card := by
  congr 1
  ext y
  simp only [mem_hammingDisagreement]
  exact ne_comm

open Classical in
/-- **Rounding a relation near a swap graph to a close cluster candidate.**
The hypotheses are stated for the relation `U`: its edit count against the
graph of `b.swapPerm` and its diagonal boundary for the union labels. -/
theorem repairRelation_extractCrossing_candidate_and_close
    [Fintype L] [DecidableEq L]
    (actX : L → Equiv.Perm X) (actZ : L → Equiv.Perm Z) {hc h' : ℝ} {m : ℕ}
    (hX : DirectedCoarea.HasCheegerLowerBound X (Finset.univ.image actX) hc)
    (hZ : DirectedCoarea.HasCheegerLowerBound Z (Finset.univ.image actZ) hc)
    (b : FinitePartialBijection X Z) (U : Finset (sumModel X Z × sumModel X Z))
    (E : ℕ)
    (hE : (permutationGraph (sumModel X Z) b.swapPerm \ U).card +
      (U \ permutationGraph (sumModel X Z) b.swapPerm).card ≤ E)
    (hsmallX : 2 * (b.sourceDefect + 3 * E) ≤ Fintype.card X)
    (hsmallZ : 2 * (b.targetDefect + 3 * E) ≤ Fintype.card Z)
    (hclose : b.sourceDefect + b.targetDefect + 6 * E < 2 * m)
    (hforward :
      (2 * (Fintype.card L : ℝ) + hc * Fintype.card L) *
          ((hc + 7 * (Finset.univ.image (sumAction actX actZ)).card) *
            ((relationBoundary (sumModel X Z)
              (Finset.univ.image (sumAction actX actZ)) U).card : ℝ)) <
        hc * hc * (h' * m / 2)) :
    (extractCrossing (repairRelation (sumModel X Z) U)).IsClusterCandidate
        actX actZ h' m ∧
      b.twoSidedDisagreement (extractCrossing (repairRelation (sumModel X Z) U)) <
        2 * m := by
  classical
  have hhc : 0 < hc := hX.1
  have hPX : HasL1PoincareAtOne X
      ((Finset.univ.image (sumAction actX actZ)).image leftPart) hc := by
    rw [image_leftPart_image_sumAction]
    exact hasL1PoincareAtOne_of_cheeger X _ hX
  have hPZ : HasL1PoincareAtOne Z
      ((Finset.univ.image (sumAction actX actZ)).image rightPart) hc := by
    rw [image_rightPart_image_sumAction]
    exact hasL1PoincareAtOne_of_cheeger Z _ hZ
  have heditsX :
      2 * ((permutationGraph (sumModel X Z) b.swapPerm \ U).card +
        (U \ permutationGraph (sumModel X Z) b.swapPerm).card) ≤ Fintype.card X := by
    omega
  have heditsZ :
      2 * ((permutationGraph (sumModel X Z) b.swapPerm \ U).card +
        (U \ permutationGraph (sumModel X Z) b.swapPerm).card) ≤ Fintype.card Z := by
    omega
  have hF : FiberCoarea (sumModel X Z) (Finset.univ.image (sumAction actX actZ)) U hc :=
    fiberCoarea_sum _ (image_sumAction_preserves actX actZ) hPX hPZ U b.swapPerm
      heditsX heditsZ
  have hbad := repairRelation_badArcs_mul_le_boundary_of_fiberCoarea
    (sumModel X Z) (Finset.univ.image (sumAction actX actZ)) U hF
  have hham :
      (hammingDisagreement b.swapPerm (repairRelation (sumModel X Z) U)).card ≤
        3 * E := by
    have h := card_repairRelation_disagreement_le (sumModel X Z) U b.swapPerm
    rw [card_hammingDisagreement_comm]
    omega
  have hhamInv :
      (hammingDisagreement b.swapPerm⁻¹ (repairRelation (sumModel X Z) U)⁻¹).card ≤
        3 * E := by
    rw [card_hammingDisagreement_inv]
    exact hham
  have hsource := sourceDefect_extractCrossing_le b (repairRelation (sumModel X Z) U)
  have htarget := targetDefect_extractCrossing_le b (repairRelation (sumModel X Z) U)
  have hsourceHalf :
      2 * (extractCrossing (repairRelation (sumModel X Z) U)).sourceDefect ≤
        Fintype.card X := by
    omega
  have htargetHalf :
      2 * (extractCrossing (repairRelation (sumModel X Z) U)).targetDefect ≤
        Fintype.card Z := by
    omega
  have hs := cheeger_mul_sourceDefect_extractCrossing_le actX actZ hX
    (repairRelation (sumModel X Z) U) hsourceHalf
  have ht := cheeger_mul_targetDefect_extractCrossing_le actX actZ hZ
    (repairRelation (sumModel X Z) U) htargetHalf
  have hcomm := card_sumCommutationDefect_le_card_mul_badArcs
    (repairRelation (sumModel X Z) U) actX actZ
  have hcommInv := card_sumCommutationDefect_le_card_mul_badArcs
    (repairRelation (sumModel X Z) U)⁻¹ actX actZ
  rw [card_badArcs_inv] at hcommInv
  have hcommReal :
      ((sumCommutationDefect (repairRelation (sumModel X Z) U) actX actZ).card : ℝ) ≤
        (Fintype.card L : ℝ) *
          ((badArcs (sumModel X Z) (Finset.univ.image (sumAction actX actZ))
            (repairRelation (sumModel X Z) U)).card : ℝ) := by
    exact_mod_cast hcomm
  have hcommInvReal :
      ((sumCommutationDefect (repairRelation (sumModel X Z) U)⁻¹ actX actZ).card : ℝ) ≤
        (Fintype.card L : ℝ) *
          ((badArcs (sumModel X Z) (Finset.univ.image (sumAction actX actZ))
            (repairRelation (sumModel X Z) U)).card : ℝ) := by
    exact_mod_cast hcommInv
  have hLnonneg : (0 : ℝ) ≤ Fintype.card L := by positivity
  have hcoefficient : (0 : ℝ) ≤ 2 * (Fintype.card L : ℝ) + hc * Fintype.card L := by
    positivity
  have hmain :
      hc * hc * ((2 * (Fintype.card L : ℝ)) *
          (extractCrossing (repairRelation (sumModel X Z) U)).sourceDefect +
        (sumCommutationDefect (repairRelation (sumModel X Z) U) actX actZ).card) ≤
        (2 * (Fintype.card L : ℝ) + hc * Fintype.card L) *
          ((hc + 7 * (Finset.univ.image (sumAction actX actZ)).card) *
            ((relationBoundary (sumModel X Z)
              (Finset.univ.image (sumAction actX actZ)) U).card : ℝ)) := by
    have h1 := mul_le_mul_of_nonneg_left hs
      (mul_nonneg hhc.le (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hLnonneg))
    have h2 := mul_le_mul_of_nonneg_left hcommReal (mul_nonneg hhc.le hhc.le)
    have h3 := mul_le_mul_of_nonneg_left hbad hcoefficient
    nlinarith
  have hmainInv :
      hc * hc * ((2 * (Fintype.card L : ℝ)) *
          (extractCrossing (repairRelation (sumModel X Z) U)).targetDefect +
        (sumCommutationDefect (repairRelation (sumModel X Z) U)⁻¹ actX actZ).card) ≤
        (2 * (Fintype.card L : ℝ) + hc * Fintype.card L) *
          ((hc + 7 * (Finset.univ.image (sumAction actX actZ)).card) *
            ((relationBoundary (sumModel X Z)
              (Finset.univ.image (sumAction actX actZ)) U).card : ℝ)) := by
    have h1 := mul_le_mul_of_nonneg_left ht
      (mul_nonneg hhc.le (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hLnonneg))
    have h2 := mul_le_mul_of_nonneg_left hcommInvReal (mul_nonneg hhc.le hhc.le)
    have h3 := mul_le_mul_of_nonneg_left hbad hcoefficient
    nlinarith
  have hhc2 : 0 < hc * hc := mul_pos hhc hhc
  have hforwardReal :
      ((2 * (Fintype.card L *
          (extractCrossing (repairRelation (sumModel X Z) U)).sourceDefect) +
        (sumCommutationDefect (repairRelation (sumModel X Z) U) actX actZ).card : ℕ) :
          ℝ) < h' * m / 2 := by
    have hlt := lt_of_mul_lt_mul_left (hmain.trans_lt hforward) hhc2.le
    push_cast
    linarith
  have hbackwardReal :
      ((2 * (Fintype.card L *
          (extractCrossing (repairRelation (sumModel X Z) U)).targetDefect) +
        (sumCommutationDefect (repairRelation (sumModel X Z) U)⁻¹ actX actZ).card : ℕ) :
          ℝ) < h' * m / 2 := by
    have hlt := lt_of_mul_lt_mul_left (hmainInv.trans_lt hforward) hhc2.le
    push_cast
    linarith
  have hself :
      (extractCrossing (repairRelation (sumModel X Z) U)).sourceDefect +
          (extractCrossing (repairRelation (sumModel X Z) U)).targetDefect < 2 * m := by
    omega
  refine ⟨isClusterCandidate_extractCrossing_of_bounds
    (repairRelation (sumModel X Z) U) actX actZ hself hforwardReal hbackwardReal, ?_⟩
  have hdist := twoSidedDisagreement_extractCrossing_le b (repairRelation (sumModel X Z) U)
  omega

end CentralizerNormalizationCrossingRepair
end GroupApproximation
