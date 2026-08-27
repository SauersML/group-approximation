import GroupApproximation.Manuscript.MFRecognition.ThreeGeneratorBridgePresentation

/-!
# Effectivity of the printed two-sided three-generator bridge

This file turns the literal presentation in
`ThreeGeneratorBridgePresentation` into a primitive-recursively searchable
relator set.  The edge family is enumerated as `0,1,-1,2,-2,...`; both every
edge relator and its inverse occur in `hnnFam`, so the resulting set is
symmetric.  The final section transfers its recursively enumerable word
problem to the manuscript's three-letter quotient map `qC`.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace Bridge
namespace Effectivity

open GroupApproximation.Higman
open GroupApproximation.Higman.HNNEmb
open Presentation
namespace BP
export GroupApproximation.Higman.BridgePresentation
  (baseRels optionNatEquiv cycle cycle_zero cycle_one cycle_two cycle_add_three
    primrec_cycle numbered_base_relator relabel_base_word normalClosureEquiv
    normalClosureEquiv_mk normalClosureEquiv_of freeEval_aRaw srcWord
    optionNatEquiv_none optionNatEquiv_some)
end BP

/-! ## Raw words for the two-sided edge family -/

/-- `x^(k+1) y x^(-(k+1))`, written as a raw word. -/
def positiveRaw (k : ℕ) : RawWord :=
  Nat.rec (motive := fun _ ↦ RawWord)
    [((0 : ℕ), true), ((1 : ℕ), true), ((0 : ℕ), false)]
    (fun _ ih ↦ ((0, true) : ℕ × Bool) :: (ih ++ [((0 : ℕ), false)])) k

@[simp] theorem positiveRaw_zero :
    positiveRaw 0 = [((0 : ℕ), true), ((1 : ℕ), true), ((0 : ℕ), false)] := rfl

@[simp] theorem positiveRaw_succ (k : ℕ) :
    positiveRaw (k + 1) =
      ((0, true) : ℕ × Bool) :: (positiveRaw k ++ [((0 : ℕ), false)]) := rfl

theorem freeEval_positiveRaw (k : ℕ) :
    freeEval (positiveRaw k) =
      FreeGroup.of 0 ^ ((k + 1 : ℕ) : ℤ) * FreeGroup.of 1 *
        FreeGroup.of 0 ^ (-((k + 1 : ℕ) : ℤ)) := by
  induction k with
  | zero =>
      unfold freeEval
      simp
      group
  | succ k ih =>
      rw [positiveRaw_succ]
      unfold freeEval at ih ⊢
      rw [evalRaw_cons, evalRaw_append, ih]
      simp only [evalRaw_cons, evalRaw_nil, if_true, mul_one]
      push_cast
      group

/-- The raw word for `x^(edgeIndex n) y x^(-edgeIndex n)`. -/
def yRaw (n : ℕ) : RawWord :=
  if n % 2 = 0 then BridgeWP.aRaw (n / 2) else positiveRaw (n / 2)

theorem freeEval_yRaw (n : ℕ) : freeEval (yRaw n) = srcWord n := by
  by_cases hn : n % 2 = 0
  · have hindex : edgeIndex n = -((n / 2 : ℕ) : ℤ) := by
      rw [edgeIndex, if_pos hn]
    rw [yRaw, if_pos hn, BP.freeEval_aRaw]
    unfold BP.srcWord srcWord
    rw [hindex]
    simp only [neg_neg]
  · have hindex : edgeIndex n = ((n / 2 + 1 : ℕ) : ℤ) := by
      rw [edgeIndex, if_neg hn]
    rw [yRaw, if_neg hn, freeEval_positiveRaw]
    unfold srcWord
    rw [hindex]

/-- The raw target word.  In the positive branch the appropriate generator of
`C` occupies old alphabet position `k+3`; in the nonpositive branch the target
equals the source. -/
def targetRaw (n : ℕ) : RawWord :=
  if n % 2 = 0 then yRaw n
  else (((n / 2 + 3 : ℕ), true) : ℕ × Bool) :: yRaw n

theorem freeEval_targetRaw (n : ℕ) :
    freeEval (targetRaw n) =
      if n % 2 = 0 then srcWord n
      else FreeGroup.of (n / 2 + 3) * srcWord n := by
  by_cases hn : n % 2 = 0
  · rw [targetRaw, if_pos hn, if_pos hn, freeEval_yRaw]
  · rw [targetRaw, if_neg hn, if_neg hn]
    unfold freeEval
    rw [evalRaw_cons]
    change FreeGroup.of (n / 2 + 3) * freeEval (yRaw n) = _
    rw [freeEval_yRaw]

/-- The old-alphabet HNN relator `t y_i t⁻¹ (c_i y_i)⁻¹`. -/
def hnnRaw (n : ℕ) : RawWord :=
  (((2 : ℕ), true) :: yRaw n) ++
    (((2 : ℕ), false) :: invRaw (targetRaw n))

/-- Every edge relator and its inverse, interleaved. -/
def hnnFam (n : ℕ) : RawWord :=
  cond (decide (n % 2 = 0)) (hnnRaw (n / 2)) (invRaw (hnnRaw (n / 2)))

theorem hnnFam_even {n : ℕ} (h : n % 2 = 0) :
    hnnFam n = hnnRaw (n / 2) := by simp [hnnFam, h]

theorem hnnFam_odd {n : ℕ} (h : ¬n % 2 = 0) :
    hnnFam n = invRaw (hnnRaw (n / 2)) := by simp [hnnFam, h]

/-- Shift the base word problem past `x,y,t`, and add the two-sided edge
relators. -/
def relSet {C : Type} [Group C] (g : ℕ → C) : Set (FreeGroup ℕ) :=
  (FreeGroup.map fun k ↦ k + 3) '' BridgeWP.wordSet g ∪
    Set.range fun n ↦ freeEval (hnnFam n)

theorem inv_mem_relSet {C : Type} [Group C] (g : ℕ → C) {z : FreeGroup ℕ}
    (hz : z ∈ relSet g) : z⁻¹ ∈ relSet g := by
  rcases hz with ⟨u, hu, rfl⟩ | ⟨n, rfl⟩
  · refine Or.inl ⟨u⁻¹, BridgeWP.inv_mem_wordSet g hu, map_inv _ _⟩
  · by_cases hpar : n % 2 = 0
    · refine Or.inr ⟨2 * (n / 2) + 1, ?_⟩
      have hidx : (2 * (n / 2) + 1) / 2 = n / 2 := by omega
      change freeEval (hnnFam (2 * (n / 2) + 1)) =
        (freeEval (hnnFam n))⁻¹
      rw [hnnFam_odd (n := 2 * (n / 2) + 1) (by omega), hidx,
        hnnFam_even hpar, BridgeWP.freeEval_invRaw]
    · refine Or.inr ⟨2 * (n / 2), ?_⟩
      have hidx : 2 * (n / 2) / 2 = n / 2 := by omega
      change freeEval (hnnFam (2 * (n / 2))) = (freeEval (hnnFam n))⁻¹
      rw [hnnFam_even (n := 2 * (n / 2)) (by omega), hidx,
        hnnFam_odd hpar, BridgeWP.freeEval_invRaw, inv_inv]

theorem symmetrize_relSet {C : Type} [Group C] (g : ℕ → C) :
    symmetrize (relSet g) = relSet g := by
  refine Set.union_eq_self_of_subset_right ?_
  rintro _ ⟨z, hz, rfl⟩
  exact inv_mem_relSet g hz

/-! ## Primitive-recursive enumeration -/

theorem primrec_positiveRaw : Primrec positiveRaw := by
  have h : Primrec fun p : ℕ × RawWord ↦
      ((0, true) : ℕ × Bool) :: (p.2 ++ [((0 : ℕ), false)]) :=
    Primrec.list_cons.comp (Primrec.const ((0, true) : ℕ × Bool))
      (Primrec.list_append.comp Primrec.snd (Primrec.const [((0 : ℕ), false)]))
  exact Primrec.nat_rec₁ _ h.to₂

theorem primrec_yRaw : Primrec yRaw := by
  have hhalf : Primrec fun n : ℕ ↦ n / 2 :=
    Primrec.nat_div.comp Primrec.id (Primrec.const 2)
  have hcond : Primrec fun n : ℕ ↦ decide (n % 2 = 0) :=
    (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2))
      (Primrec.const 0)).decide
  refine (Primrec.cond hcond (BridgeWP.primrec_aRaw.comp hhalf)
    (primrec_positiveRaw.comp hhalf)).of_eq fun n => ?_
  unfold yRaw
  by_cases hn : n % 2 = 0 <;> simp [hn]

theorem primrec_targetRaw : Primrec targetRaw := by
  have hhalf : Primrec fun n : ℕ ↦ n / 2 :=
    Primrec.nat_div.comp Primrec.id (Primrec.const 2)
  have hcond : Primrec fun n : ℕ ↦ decide (n % 2 = 0) :=
    (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2))
      (Primrec.const 0)).decide
  have hhead : Primrec fun n : ℕ ↦ (((n / 2 + 3 : ℕ), true) : ℕ × Bool) :=
    Primrec.pair
      (Primrec.nat_add.comp hhalf (Primrec.const 3)) (Primrec.const true)
  refine (Primrec.cond hcond primrec_yRaw
    (Primrec.list_cons.comp hhead primrec_yRaw)).of_eq fun n => ?_
  unfold targetRaw
  by_cases hn : n % 2 = 0 <;> simp [hn]

theorem primrec_hnnRaw : Primrec hnnRaw := by
  have h1 : Primrec fun n : ℕ ↦ (((2 : ℕ), true) : ℕ × Bool) :: yRaw n :=
    Primrec.list_cons.comp (Primrec.const (((2 : ℕ), true) : ℕ × Bool)) primrec_yRaw
  have h2 : Primrec fun n : ℕ ↦ (((2 : ℕ), false) : ℕ × Bool) ::
      invRaw (targetRaw n) :=
    Primrec.list_cons.comp (Primrec.const (((2 : ℕ), false) : ℕ × Bool))
      (primrec_invRaw.comp primrec_targetRaw)
  exact Primrec.list_append.comp h1 h2

theorem primrec_hnnFam : Primrec hnnFam := by
  have hhalf : Primrec fun n : ℕ ↦ n / 2 :=
    Primrec.nat_div.comp Primrec.id (Primrec.const 2)
  have hcond : Primrec fun n : ℕ ↦ decide (n % 2 = 0) :=
    (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2))
      (Primrec.const 0)).decide
  exact Primrec.cond hcond (primrec_hnnRaw.comp hhalf)
    (primrec_invRaw.comp (primrec_hnnRaw.comp hhalf))

theorem search_relSet {C : Type} [Group C] (g : ℕ → C)
    (hre : REPred fun w : RawWord ↦ evalRaw g w = 1) :
    ∃ f : RawWord → ℕ → Bool, Primrec₂ f ∧
      ∀ v : RawWord, freeEval v ∈ relSet g ↔ ∃ n, f v n = true := by
  unfold relSet
  obtain ⟨F, hF, hFspec⟩ := exists_primrec_of_rePred hre
  have hword : ∀ v : RawWord, freeEval v ∈ BridgeWP.wordSet g ↔
      ∃ n, F v n = true := by
    intro v
    rw [BridgeWP.mem_wordSet_iff]
    exact hFspec v
  have hshift : Primrec fun k : ℕ ↦ k + 3 :=
    Primrec.nat_add.comp Primrec.id (Primrec.const 3)
  obtain ⟨f₁, hf₁, hf₁spec⟩ := search_image hshift hF hword
  obtain ⟨f₁', hf₁', hf₁'spec⟩ := search_reindex f₁ hf₁
  obtain ⟨f₂', hf₂', hf₂'spec⟩ :=
    search_reindex (fun (v : RawWord) (p : ℕ × List ℕ) ↦
      decide (Computability.applySteps (hnnFam p.1 ++ invRaw v) p.2 = some []))
      (primrec_rangeSearch primrec_hnnFam)
  refine search_union hf₁' hf₂' (fun v ↦ ?_) (fun v ↦ ?_)
  · exact (hf₁spec v).trans (hf₁'spec v)
  · refine (mem_range_iff_search hnnFam v).trans (Iff.trans ?_ (hf₂'spec v))
    exact exists_congr fun _ ↦ decide_eq_true_iff.symm

/-! ## Match the literal HNN presentation -/

/-- Rename the searchable old alphabet `(x,y,t,c₀,...)` to the literal
presentation alphabet `(t,x,y,c₀,...)`. -/
def codedRels {C : Type} [Group C] (g : ℕ → C) : Set (FreeGroup ℕ) :=
  FreeGroup.map BP.cycle '' relSet g

theorem map_cycle_yRaw (n : ℕ) :
    FreeGroup.map BP.cycle (freeEval (yRaw n)) =
      FreeGroup.map BP.optionNatEquiv (HNNPresentation.emb (srcWord n)) := by
  rw [freeEval_yRaw]
  unfold srcWord
  simp only [map_mul, map_zpow, FreeGroup.map.of, BP.cycle_zero, BP.cycle_one,
    HNNPresentation.emb, BP.optionNatEquiv_some]

theorem map_cycle_srcWord (n : ℕ) :
    FreeGroup.map BP.cycle (srcWord n) =
      FreeGroup.map BP.optionNatEquiv (HNNPresentation.emb (srcWord n)) := by
  calc
    FreeGroup.map BP.cycle (srcWord n) =
        FreeGroup.map BP.cycle (freeEval (yRaw n)) := by rw [freeEval_yRaw]
    _ = FreeGroup.map BP.optionNatEquiv (HNNPresentation.emb (srcWord n)) :=
      map_cycle_yRaw n

theorem map_cycle_targetRaw (n : ℕ) :
    FreeGroup.map BP.cycle (freeEval (targetRaw n)) =
      FreeGroup.map BP.optionNatEquiv (HNNPresentation.emb (tgtWord n)) := by
  rw [freeEval_targetRaw]
  by_cases hn : n % 2 = 0
  · rw [if_pos hn, tgtWord, if_pos hn, map_cycle_srcWord]
  · rw [if_neg hn, tgtWord, if_neg hn]
    simp only [map_mul, FreeGroup.map.of, BP.cycle_add_three]
    rw [map_cycle_srcWord]
    simp only [HNNPresentation.emb, BP.optionNatEquiv_some, FreeGroup.map.of]

theorem map_cycle_hnnRaw (n : ℕ) :
    FreeGroup.map BP.cycle (freeEval (hnnRaw n)) =
      FreeGroup.map BP.optionNatEquiv
        (HNNPresentation.stableWord * HNNPresentation.emb (srcWord n) *
          HNNPresentation.stableWord⁻¹ * (HNNPresentation.emb (tgtWord n))⁻¹) := by
  have hold : freeEval (hnnRaw n) =
      FreeGroup.of 2 * freeEval (yRaw n) * (FreeGroup.of 2)⁻¹ *
        (freeEval (targetRaw n))⁻¹ := by
    unfold hnnRaw freeEval
    rw [evalRaw_append]
    simp
    group
  rw [hold]
  simp only [map_mul, map_inv, FreeGroup.map.of, BP.cycle_two,
    HNNPresentation.stableWord, BP.optionNatEquiv_none]
  rw [map_cycle_yRaw, map_cycle_targetRaw]

theorem hnnNumberedRels_subset_coded {C : Type} [Group C] (g : ℕ → C) :
    Presentation.hnnNumberedRels g ⊆ codedRels g := by
  rintro r ⟨s, hs, rfl⟩
  rcases hs with ⟨u, hu, rfl⟩ | ⟨n, rfl⟩
  · rcases hu with ⟨v, hv, rfl⟩
    rcases hv with ⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩
    · refine ⟨FreeGroup.map (fun k : ℕ ↦ k + 3) w,
        Or.inl ⟨w, hw, rfl⟩, ?_⟩
      rw [BP.relabel_base_word]
      exact (BP.numbered_base_relator w).symm
    · exact hw.elim
  · refine ⟨freeEval (hnnRaw n), Or.inr ⟨2 * n, ?_⟩, map_cycle_hnnRaw n⟩
    change freeEval (hnnFam (2 * n)) = freeEval (hnnRaw n)
    rw [hnnFam_even (n := 2 * n) (by omega)]
    congr 2
    omega

theorem codedRels_subset_normalClosure {C : Type} [Group C] (g : ℕ → C) :
    codedRels g ⊆ Subgroup.normalClosure (Presentation.hnnNumberedRels g) := by
  rintro r ⟨s, hs, rfl⟩
  rcases hs with ⟨u, hu, rfl⟩ | ⟨n, rfl⟩
  · rw [← BP.numbered_base_relator u]
    exact Subgroup.subset_normalClosure
      ⟨HNNPresentation.emb (FreeGroup.map (fun k : ℕ ↦ k + 2) u),
        Or.inl ⟨FreeGroup.map (fun k : ℕ ↦ k + 2) u,
          ⟨FreeGroup.map Sum.inl u, Or.inl ⟨u, hu, rfl⟩,
            BP.relabel_base_word u⟩, rfl⟩, rfl⟩
  · by_cases h : n % 2 = 0
    · change FreeGroup.map BP.cycle (freeEval (hnnFam n)) ∈ _
      rw [hnnFam_even h, map_cycle_hnnRaw]
      exact Subgroup.subset_normalClosure ⟨_, Or.inr ⟨n / 2, rfl⟩, rfl⟩
    · change FreeGroup.map BP.cycle (freeEval (hnnFam n)) ∈ _
      rw [hnnFam_odd h, BridgeWP.freeEval_invRaw, map_inv, map_cycle_hnnRaw]
      exact Subgroup.inv_mem _
        (Subgroup.subset_normalClosure ⟨_, Or.inr ⟨n / 2, rfl⟩, rfl⟩)

theorem normalClosure_numbered_eq_coded {C : Type} [Group C] (g : ℕ → C) :
    Subgroup.normalClosure (Presentation.hnnNumberedRels g) =
      Subgroup.normalClosure (codedRels g) := by
  apply le_antisymm
  · exact Subgroup.normalClosure_mono (hnnNumberedRels_subset_coded g)
  · exact Subgroup.normalClosure_le_normal (codedRels_subset_normalClosure g)

noncomputable def extEquivCoded {C : Type} [Group C] (g : ℕ → C)
    (hspan : Subgroup.closure (Set.range g) = ⊤) :
    BGroup (seq g) ≃* PresentedGroup (codedRels g) :=
  (Presentation.extEquivNumbered g hspan).trans
    (BP.normalClosureEquiv (normalClosure_numbered_eq_coded g))

end Effectivity
end Bridge
end MFRecognition
end Manuscript
end GroupApproximation
