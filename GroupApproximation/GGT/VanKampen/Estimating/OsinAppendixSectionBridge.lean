import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSections
import GroupApproximation.GroupTheory.NormalClosureReducedProduct
import GroupApproximation.Meta.AxiomGuard

/-!
# Distinguished section systems exist, and Lemma 9.7 at one section is `Gr0`

Consequences of the vocabulary in `Estimating/OsinAppendixSections.lean`.

* `DiscDiagram.reduced_of_leastArea`: Osin's reducedness (least area) implies
  the algebraic `DiscDiagram.Reduced`.  A cancelling pair could be deleted from
  the ordered cell values, leaving a relator product of the boundary value with
  two fewer factors (`RelatorDefectBudget.no_cancelling_pair_of_minimal`).
* `relativeGreendlingerQuasiGeodesicLeastArea_of_reduced`: the historical waist
  `RelativeGreendlingerQuasiGeodesicStatement` implies the least-area waist.
* `exists_globallyDistinguishedSectionFamily`: Osin's distinguished system
  (Definition 9.2) over every reduced O-equivalent diagram exists.  The total
  weight of a compatible family is bounded by the relator perimeters plus the
  boundary length (`RegionCandidate.familyWeight_le`), and the empty family is
  admissible, so the maximum is attained; well-ordering then attains the minimal
  cardinality.  This is the pattern of `RegionGlobalSelection`, restricted to
  section-respecting regions.
* `relativeGreendlingerQuasiGeodesicLeastArea_of_osinLemma97`: clause (b) of
  Lemma 9.7 at the single section `SectionCuts.whole` is Osin's Lemma 4.4 at
  least-area diagrams, `RelativeGreendlingerQuasiGeodesicLeastAreaStatement`.
  The one present region is read as an embedded `Contiguity`
  (`RegionCandidate.toContiguityOfTargetNone`): both of the historical O52 fields
  are vacuous for an outer target.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded

/-! ## Least area is reducedness -/

/-- **Least area implies the algebraic reducedness.**  The ordered cell values
form a relator product of the boundary value, and a cancelling pair could be
deleted from it. -/
theorem DiscDiagram.reduced_of_leastArea {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {Delta : DiscDiagram.{u, w, v} W}
    (hlea : Delta.LeastArea) : Delta.Reduced := by
  intro pre between suf C₁ C₂ hsplit
  have hcells : ∀ x ∈ Delta.relatorCells.map RelatorCell.value,
      RelatorDefectBudget.IsSignedConjugate (RelLetter.listVal '' W) x := by
    intro x hx
    obtain ⟨C, _hC, rfl⟩ := List.mem_map.mp hx
    refine ⟨C.conjugator, RelLetter.listVal C.word, ⟨C.word, C.word_mem, rfl⟩, ?_⟩
    rcases hrev : C.reversed with _ | _
    · left
      simp [RelatorCell.value, hrev]
    · right
      simp [RelatorCell.value, hrev]
  exact RelatorDefectBudget.no_cancelling_pair_of_minimal
    (n := Delta.rCellCount) (w := Delta.boundaryValue)
    (factors := Delta.relatorCells.map RelatorCell.value)
    (by simp [DiscDiagram.rCellCount])
    Delta.relatorValues_prod_eq_boundaryValue hcells (fun h => hlea h)
    (pre.map RelatorCell.value) (between.map RelatorCell.value)
    (suf.map RelatorCell.value) C₁.value C₂.value
    (by rw [hsplit]; simp only [List.map_append, List.map_cons])

/-- **The historical waist implies the least-area waist**, since least area is a
stronger hypothesis than algebraic reducedness. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_reduced
    (h : RelativeGreendlingerQuasiGeodesicStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨eps, rho, hrho, hgood⟩ :=
    h D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  exact ⟨eps, rho, hrho, fun W hcondition Delta hlea hcells hboundary =>
    hgood W hcondition Delta (DiscDiagram.reduced_of_leastArea hlea) hcells
      hboundary⟩

/-! ## Distinguished section systems exist -/

namespace RealizedSectionFamily

/-- A section family's weight obeys the perimeter bound of its region family. -/
theorem weight_le {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (S : RealizedSectionFamily D lambda c eps Delta cuts) :
    S.weight ≤ (∑ i : Fin Delta.rCellCount, (cell Delta i).word.length) +
      Delta.boundaryWord.length :=
  S.toRealizedRegionFamily.weight_le

/-- The empty section family on the diagram itself. -/
def empty {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (Delta : DiscDiagram.{u, w, v} W)
    (cuts : SectionCuts D lambda c Delta.boundaryWord) (hred : Delta.Reduced) :
    RealizedSectionFamily D lambda c eps Delta cuts where
  toRealizedRegionFamily := RealizedRegionFamily.empty D eps Delta hred
  respects := by
    intro a ha
    simp [RealizedRegionFamily.empty] at ha

end RealizedSectionFamily

/-- **Osin's distinguished system exists** over every reduced O-equivalent
diagram, with sections. -/
theorem exists_globallyDistinguishedSectionFamily
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (Delta : DiscDiagram.{u, w, v} W)
    (cuts : SectionCuts D lambda c Delta.boundaryWord) (hred : Delta.Reduced) :
    Nonempty (GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) := by
  classical
  let bound := (∑ i : Fin Delta.rCellCount, (cell Delta i).word.length) +
    Delta.boundaryWord.length
  let values := (Finset.range (bound + 1)).filter fun n =>
    ∃ S : RealizedSectionFamily D lambda c eps Delta cuts, S.weight = n
  have hmem (S : RealizedSectionFamily D lambda c eps Delta cuts) :
      S.weight ∈ values := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, S, rfl⟩
    have h := S.weight_le
    change S.weight ≤ bound at h
    omega
  have hnonempty : values.Nonempty :=
    ⟨(RealizedSectionFamily.empty D lambda c eps Delta cuts hred).weight,
      hmem (RealizedSectionFamily.empty D lambda c eps Delta cuts hred)⟩
  obtain ⟨maximum, hmaximum, hmaximal⟩ :=
    Finset.exists_max_image values id hnonempty
  obtain ⟨initial, hinitial⟩ := (Finset.mem_filter.mp hmaximum).2
  have hexists : ∃ k : ℕ, ∃ S : RealizedSectionFamily D lambda c eps Delta cuts,
      S.weight = maximum ∧ S.family.card = k :=
    ⟨initial.family.card, initial, hinitial, rfl⟩
  obtain ⟨S, hweight, hcard⟩ := Nat.find_spec hexists
  refine ⟨{ toRealizedSectionFamily := S, weight_maximal := ?_, card_minimal := ?_ }⟩
  · intro other
    rw [hweight]
    exact hmaximal other.weight (hmem other)
  · intro other heq
    rw [hcard]
    apply Nat.find_min' hexists
    exact ⟨other, heq.trans hweight, rfl⟩

/-! ## One section is Osin's Lemma 4.4 -/

/-- An exterior region read as an embedded contiguity.  Both historical O52
fields quantify over a relator-cell target, so they are vacuous here. -/
def Embedded.RegionCandidate.toContiguityOfTargetNone
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (a : RegionCandidate D eps Delta) (ht : a.2.target = none) :
    Contiguity D eps Delta a.1 where
  boundary := a.2.boundary
  source := a.2.source
  target := a.2.target
  sourceArc := a.2.sourceArc
  targetArc := a.2.targetArc
  rightSide := a.2.rightSide
  leftSide := a.2.leftSide
  boundary_decomposition := a.2.boundary_decomposition
  rightSide_length_le := a.2.rightSide_length_le
  leftSide_length_le := a.2.leftSide_length_le
  rightSide_norm_le := a.2.rightSide_norm_le
  leftSide_norm_le := a.2.leftSide_norm_le
  target_ne_source := fun _i hi => absurd (ht.symm.trans hi) (by simp)
  o52Certificate := fun _i hi => absurd (ht.symm.trans hi) (by simp)
  pasting := a.2.pasting

/-- **Lemma 9.7 at one section gives Osin's Lemma 4.4** at least-area diagrams,
the Greendlinger waist `RelativeGreendlingerQuasiGeodesicLeastAreaStatement`. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_osinLemma97
    (h97 : OsinLemma97SectionStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨eps0, h⟩ :=
    h97 D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨rho0, hrho0, hall⟩ := h eps0 le_rfl
  refine ⟨eps0, rho0, hrho0, ?_⟩
  intro W hcondition Delta hlea hcells hboundary
  obtain ⟨_, S, hb⟩ :=
    hall rho0 le_rfl W hcondition Delta (SectionCuts.whole hboundary) hlea hcells
  obtain ⟨_source, present, region, _hmem, _hsource, htargets, _hdistinct, hsum⟩ := hb
  have hne : present.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, Finset.sum_empty] at hsum
    linarith
  obtain ⟨j0, hj0⟩ := hne
  have hpresent : present = {j0} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨hj0, fun j _ => ?_⟩
    apply Fin.ext
    have h1 : j.val < 1 := j.isLt
    have h2 : j0.val < 1 := j0.isLt
    omega
  rw [hpresent, Finset.sum_singleton] at hsum
  have ht : (region j0).2.target = none := (htargets j0 hj0).1
  have hy : (0 : ℝ) <
      ((cell S.diagram (region j0).2.source).word.length : ℝ) := by
    rcases Nat.eq_zero_or_pos (cell S.diagram (region j0).2.source).word.length with
      h0 | hpos
    · exfalso
      unfold RegionCandidate.contiguityDegree at hsum
      rw [h0, Nat.cast_zero, div_zero] at hsum
      linarith
    · exact_mod_cast hpos
  have hlarge := (lt_div_iff₀ hy).mp hsum
  exact ⟨S.diagram, ⟨S.equiv⟩, (region j0).1,
    (region j0).toContiguityOfTargetNone ht, ht, hlarge⟩

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.DiscDiagram.reduced_of_leastArea
#audit_axioms GroupApproximation.GGT.VanKampen.relativeGreendlingerQuasiGeodesicLeastArea_of_reduced
#audit_axioms GroupApproximation.GGT.VanKampen.exists_globallyDistinguishedSectionFamily
#audit_axioms GroupApproximation.GGT.VanKampen.relativeGreendlingerQuasiGeodesicLeastArea_of_osinLemma97
