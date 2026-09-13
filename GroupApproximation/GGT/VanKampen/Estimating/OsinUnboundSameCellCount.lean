import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundSameCellBlocks
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellFactorInput
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSectionMultipleEdge
import GroupApproximation.Meta.AxiomGuard

/-!
# Same-cell unbound darts: the count along every cell, from the pocket value clause

Osin (math/0411039v3, §9), proof of Lemma 9.4.  `OsinLemma94SameCellScanInput` asks, on each
relator cell `i` of the distinguished system, for `λ · #same_i ≤ (1 - λ) · #other_i +
c · (1 + runs_i)` with at most `2 |M|` runs in total.  This module proves it from the pocket value
clause `OsinLemma94SameCellPocketInput`.
* `OsinUnboundSameCellBlocks.exists_base_scan` gives the inequality on each cell with the run starts
  of some base.
* `positionCount_starts_le`: a run start is a bound dart whose predecessor is unbound, so it is
  the first dart of a region arc on the cell (`OsinUnboundSameCellCycle.head?_eq_of_pred_not_mem`).
  The run starts number at most `arcCount family i`, one per region arc on cell `i`.
* `sum_arcCount_le`: a region has one source cell and at most one target cell, so the arcs on all
  cells number at most `2 |M|`.
* `osinLemma94SameCellScanInput_of_pocket`: the scan residual.  The optimal diagram `S.diagram` has
  least area and the same number of relator cells as `Δ`, so the pocket value clause applies to it.

## Manuscript status

Infrastructure for `thm:hull` ("Hull's small cancellation theorem", through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open scoped Classical

namespace OsinUnboundSameCellCount

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ}

/-- The number of region arcs on relator cell `i`: one per selected region with source `i`, and
one per selected region with target `i`. -/
noncomputable def arcCount {X : DiscDiagram.{u, w, v} W}
    (family : Finset (RegionCandidate D eps X)) (i : Fin X.rCellCount) : ℕ :=
  ∑ a ∈ family, ((if a.2.source = i then 1 else 0) + (if a.2.target = some i then 1 else 0))

/-- **The arcs on all cells number at most `2 |M|`.** -/
theorem sum_arcCount_le {X : DiscDiagram.{u, w, v} W}
    (family : Finset (RegionCandidate D eps X)) :
    ∑ i : Fin X.rCellCount, arcCount family i ≤ 2 * family.card := by
  unfold arcCount
  rw [Finset.sum_comm]
  calc ∑ a ∈ family, ∑ i : Fin X.rCellCount,
        ((if a.2.source = i then 1 else 0) + (if a.2.target = some i then 1 else 0))
      ≤ ∑ _a ∈ family, 2 := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [Finset.sum_add_distrib]
        have hs : ∑ i : Fin X.rCellCount, (if a.2.source = i then 1 else 0) = 1 := by simp
        have ht : ∑ i : Fin X.rCellCount, (if a.2.target = some i then 1 else 0) ≤ 1 := by
          rcases h : a.2.target with _ | j
          · simp
          · simp
        omega
    _ = 2 * family.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- **A dart of a region arc is bound.** -/
theorem not_mem_unboundDarts_of_mem_cellArcDarts {X : DiscDiagram.{u, w, v} W}
    {family : Finset (RegionCandidate D eps X)} {a : RegionCandidate D eps X} (ha : a ∈ family)
    {i : Fin X.rCellCount} {d : X.toCombMap.Dart} (hd : d ∈ a.cellArcDarts i) :
    d ∉ RegionCandidate.unboundDarts family i := by
  simp only [RegionCandidate.unboundDarts, Finset.mem_sdiff, not_and, not_not]
  intro _
  have hk : a ∈ RegionCandidate.ofKind family a.2.target.isSome :=
    Finset.mem_filter.mpr ⟨ha, rfl⟩
  have hb : d ∈ RegionCandidate.boundDarts family a.2.target.isSome i := by
    simp only [RegionCandidate.boundDarts, Finset.mem_biUnion]
    exact ⟨a, hk, hd⟩
  cases h : a.2.target.isSome
  · rw [h] at hb
    exact Finset.mem_union_left _ hb
  · rw [h] at hb
    exact Finset.mem_union_right _ hb

/-- **A bound dart of the cell lies on a region arc.** -/
theorem exists_arc_of_not_mem_unboundDarts {X : DiscDiagram.{u, w, v} W}
    {family : Finset (RegionCandidate D eps X)} {i : Fin X.rCellCount} {d : X.toCombMap.Dart}
    (hmem : d ∈ cellDarts X i) (hd : d ∉ RegionCandidate.unboundDarts family i) :
    ∃ a ∈ family, d ∈ a.cellArcDarts i := by
  simp only [RegionCandidate.unboundDarts, Finset.mem_sdiff, List.mem_toFinset, not_and,
    not_not] at hd
  rcases Finset.mem_union.mp (hd hmem) with h | h <;>
  · simp only [RegionCandidate.boundDarts, RegionCandidate.ofKind, Finset.mem_biUnion,
      Finset.mem_filter] at h
    obtain ⟨a, ⟨ha, -⟩, hda⟩ := h
    exact ⟨a, ha, hda⟩

/-- **Positions with distinct images in a finite set number at most its size.** -/
theorem positionCount_le_card {β : Type*} {p : ℕ → Prop} {n : ℕ} (g : ℕ → β) (T : Finset β)
    (hinj : ∀ a b, a < n → b < n → p a → p b → g a = g b → a = b)
    (hT : ∀ j, j < n → p j → g j ∈ T) : positionCount p 0 n ≤ T.card := by
  simp only [positionCount, Finset.sum_boole]
  have hmaps : Set.MapsTo g (((Finset.Ico 0 n).filter p : Finset ℕ) : Set ℕ) (T : Set β) := by
    intro j hj
    simp only [Finset.coe_filter, Finset.mem_Ico, Set.mem_setOf_eq] at hj
    exact Finset.mem_coe.mpr (hT j hj.1.2 hj.2)
  have hinj' : Set.InjOn g (((Finset.Ico 0 n).filter p : Finset ℕ) : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_filter, Finset.mem_Ico, Set.mem_setOf_eq] at ha hb
    exact hinj a b ha.1.2 hb.1.2 ha.2 hb.2 hab
  exact_mod_cast Finset.card_le_card_of_injOn g hmaps hinj'

/-- **The run starts on a cell number at most the region arcs on it.** -/
theorem positionCount_starts_le {X : DiscDiagram.{u, w, v} W}
    (family : Finset (RegionCandidate D eps X)) (i : Fin X.rCellCount) {k₀ : ℕ}
    (hk₀ : k₀ < (X.faceBoundary (cell X i).face).darts.length) :
    positionCount (fun j => 0 < j ∧
      (X.toCombMap.facePerm ^ j) (X.faceBoundary (cell X i).face).darts[k₀] ∉
        RegionCandidate.unboundDarts family i ∧
      ¬ (X.toCombMap.facePerm ^ (j - 1)) (X.faceBoundary (cell X i).face).darts[k₀] ∉
        RegionCandidate.unboundDarts family i) 0
      (X.faceBoundary (cell X i).face).darts.length ≤ (arcCount family i : ℝ) := by
  set B := X.faceBoundary (cell X i).face
  refine (positionCount_le_card (n := B.darts.length)
    (fun j => some ((X.toCombMap.facePerm ^ j) B.darts[k₀]))
    ((family.filter fun a => a.2.source = i).image (fun a => a.2.sourceArc.darts.head?) ∪
      (family.filter fun a => a.2.target = some i).image (fun a => a.2.targetArc.darts.head?))
    ?_ ?_).trans ?_
  · intro a b ha hb _ _ hab
    exact OsinUnboundSameCellCycle.pow_inj B hk₀ ha hb (Option.some.inj hab)
  · rintro j - ⟨hj0, hjb, hpred⟩
    have hpredU := not_not.mp hpred
    obtain ⟨a, haK, haArc⟩ :=
      exists_arc_of_not_mem_unboundDarts (OsinUnboundSameCellCycle.mem_of_pow B hk₀ j) hjb
    have hpredArc : (X.toCombMap.facePerm ^ (j - 1)) B.darts[k₀] ∉ a.cellArcDarts i :=
      fun hin => not_mem_unboundDarts_of_mem_cellArcDarts haK hin hpredU
    have hstep : X.toCombMap.facePerm ((X.toCombMap.facePerm ^ (j - 1)) B.darts[k₀]) =
        (X.toCombMap.facePerm ^ j) B.darts[k₀] := by
      have h := facePerm_pow_apply_pow X.toCombMap 1 (j - 1) B.darts[k₀]
      rw [pow_one, show 1 + (j - 1) = j by omega] at h
      exact h
    simp only [RegionCandidate.cellArcDarts, Finset.mem_union] at haArc hpredArc
    rcases haArc with h | h
    · split_ifs at h with hsrc
      · have hz : (X.toCombMap.facePerm ^ (j - 1)) B.darts[k₀] ∉ a.2.sourceArc.darts :=
          fun hin => hpredArc (Or.inl (by rw [if_pos hsrc]; exact List.mem_toFinset.mpr hin))
        have hhead := OsinUnboundSameCellCycle.head?_eq_of_pred_not_mem B
          (congrArg (cellDarts X) hsrc : cellDarts X a.2.source = B.darts) a.2.sourceArc
          (List.mem_toFinset.mp h) hstep hz
        exact Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨haK, hsrc⟩, hhead⟩)
      · simp at h
    · split_ifs at h with htgt
      · have hz : (X.toCombMap.facePerm ^ (j - 1)) B.darts[k₀] ∉ a.2.targetArc.darts :=
          fun hin => hpredArc (Or.inr (by rw [if_pos htgt]; exact List.mem_toFinset.mpr hin))
        have hhead := OsinUnboundSameCellCycle.head?_eq_of_pred_not_mem B
          (congrArg (targetDarts X) htgt : targetDarts X a.2.target = B.darts) a.2.targetArc
          (List.mem_toFinset.mp h) hstep hz
        exact Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨haK, htgt⟩, hhead⟩)
      · simp at h
  · have hle : ((family.filter fun a => a.2.source = i).image
        (fun a => a.2.sourceArc.darts.head?) ∪
        (family.filter fun a => a.2.target = some i).image
          (fun a => a.2.targetArc.darts.head?)).card ≤ arcCount family i := by
      refine (Finset.card_union_le _ _).trans
        ((Nat.add_le_add Finset.card_image_le Finset.card_image_le).trans (le_of_eq ?_))
      rw [arcCount, Finset.sum_add_distrib, Finset.card_filter, Finset.card_filter]
    exact_mod_cast hle

end OsinUnboundSameCellCount

/-- **The scan along each cell from the pocket value clause.**  With the pocket value clause at
the parameters of Lemma 9.4, the scan residual `OsinLemma94SameCellScanInput` holds, with the run
counts `arcCount`. -/
theorem osinLemma94SameCellScanInput_of_pocket
    (hpocket : OsinLemma94SameCellPocketInput.{u, w, v}) :
    OsinLemma94SameCellScanInput.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16 eps
  obtain ⟨rho1, hrho1, hP⟩ := hpocket D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16 eps
  refine ⟨max rho1 (⌈c / lambda⌉₊ + 2), lt_of_lt_of_le hrho1 (le_max_left _ _),
    fun rho hrho W hW Delta cuts hleast hcells hbelow S hcard hmin => ?_⟩
  have hrho2 : ⌈c / lambda⌉₊ + 2 ≤ rho := (max_le_iff.mp hrho).2
  have hrhoc : c < lambda * rho := by
    have hceil : c / lambda ≤ ⌈c / lambda⌉₊ := Nat.le_ceil _
    have hcast : ((⌈c / lambda⌉₊ : ℕ) : ℝ) + 1 ≤ rho := by
      exact_mod_cast (by omega : ⌈c / lambda⌉₊ + 1 ≤ rho)
    have hlt : c < rho * lambda := (div_lt_iff₀ hlambda).mp (by linarith)
    linarith [mul_comm lambda (rho : ℝ)]
  have hvalue := S.cell_listVal_ne_one hW hlambda hrhoc
  have hleastX : S.diagram.LeastArea := S.equiv.leastArea hleast
  have hbelowX : ∀ (Xi : DiscDiagram.{u, w, v} W)
      (cutsXi : SectionCuts D lambda c Xi.boundaryWord),
      Xi.LeastArea → 0 < Xi.rCellCount → Xi.rCellCount < S.diagram.rCellCount →
        ∃ T : RealizedSectionFamily D lambda c eps Xi cutsXi, OsinLemma97bConclusion mu T :=
    fun Xi cutsXi h1 h2 h3 => hbelow Xi cutsXi h1 h2 (h3.trans_eq S.equiv.rCellCount_eq)
  have hpv : OsinUnboundSameCellBlocks.PocketValue S.diagram :=
    hP rho (max_le_iff.mp hrho).1 W hW S.diagram hleastX hbelowX
  refine ⟨fun i => OsinUnboundSameCellCount.arcCount S.family i,
    OsinUnboundSameCellCount.sum_arcCount_le S.family, fun i => ?_⟩
  obtain ⟨k₀, hk₀, hscan⟩ := OsinUnboundSameCellBlocks.exists_base_scan hW hlambda.le hlambda1
    hc hvalue hpv S.family i
  have hstarts := OsinUnboundSameCellCount.positionCount_starts_le S.family i hk₀
  have hmul := mul_le_mul_of_nonneg_left (add_le_add_left hstarts 1) hc
  show _ ≤ _ + c * (1 + (OsinUnboundSameCellCount.arcCount S.family i : ℝ))
  linarith

#audit_axioms GroupApproximation.GGT.VanKampen.OsinUnboundSameCellCount.sum_arcCount_le
#audit_axioms GroupApproximation.GGT.VanKampen.OsinUnboundSameCellCount.not_mem_unboundDarts_of_mem_cellArcDarts
#audit_axioms GroupApproximation.GGT.VanKampen.OsinUnboundSameCellCount.exists_arc_of_not_mem_unboundDarts
#audit_axioms GroupApproximation.GGT.VanKampen.OsinUnboundSameCellCount.positionCount_le_card
#audit_axioms GroupApproximation.GGT.VanKampen.OsinUnboundSameCellCount.positionCount_starts_le
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94SameCellScanInput_of_pocket

end GroupApproximation.GGT.VanKampen
