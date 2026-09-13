import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PolygonClasses
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PolygonCovers
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94RegionSideCount
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.4: the class cover from the end loops

Osin (math/0411039v3, §9), proof of Lemma 9.4: "Let `S_i` denote the sum of lengths of all arcs
of type (A1) in `∂Δ_i`, `i = 1, …, d`. [...] Indeed otherwise we have
`S = ∑_{i=1}^d S_i ≤ (√ρ / 60) ∑_{i=1}^d n_i < n √ρ`."

`OsinLemma94ClassPolygons.ClassCovers L` covers the unbound darts by the (A1) class words of the
polygons with at least two classes, up to `L n`.  A polygon with a single class is dropped
there, so an unbound dart across one of its (A1) sides has to be covered some other way.
`OsinLemma94ClassPolygons.classCovers_of_endLoops` proves `ClassCovers (24 ε + 2 (K + 24) B + T)`
from the class budget `K` and these facts about `Q`.
* At most `T n` unbound darts have their own cell across.
* Every other unbound dart facing no selected region lies across an (A1) side of a polygon.
* If that polygon has a single class, the reverse dart lies in an (A1) class of a polygon with at
  least two classes, or in an end loop: two per class of a budget polygon, four per selected
  region.  Every end loop has at most `B` darts.

The count has four parts.
* The unbound darts facing a selected region number at most `2 ε |M| ≤ 24 ε n`
  (`RealizedSectionFamily.sum_card_regionFacingUnbound_le`).
* The unbound darts with their own cell across number at most `T n`.
* An (A1) side of a polygon with at least two classes lies in an (A1) class, whose darts contain
  those of the side (`OsinLemma94ClassPolygons.exists_class_of_relatorSide`).  The (A1) classes
  carry at most `∑ S_i` darts.
* The end loops carry at most `2 K n B + 4 |M| B ≤ 2 (K + 24) n B` darts.
Reversal is injective and distinct cells have disjoint darts, so the reversed darts are counted
once.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open scoped Classical

namespace OsinLemma94ClassCovers

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- The unbound darts of cell `i` with cell `i` across. -/
noncomputable def sameCellUnbound (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (i : Fin S.diagram.rCellCount) : Finset S.diagram.toCombMap.Dart :=
  (RegionCandidate.unboundDarts S.family i).filter fun d =>
    (cell S.diagram i).face = S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d)

/-- The unbound darts of cell `i` facing no selected region, with no cell `i` across. -/
noncomputable def otherCellOffRegions
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (i : Fin S.diagram.rCellCount) : Finset S.diagram.toCombMap.Dart :=
  (S.unboundOffRegions i).filter fun d =>
    (cell S.diagram i).face ≠ S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d)

theorem mem_cellDarts_of_mem_otherCellOffRegions
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    {i : Fin S.diagram.rCellCount} {d : S.diagram.toCombMap.Dart}
    (hd : d ∈ otherCellOffRegions S i) : d ∈ cellDarts S.diagram i :=
  List.mem_toFinset.mp
    (Finset.mem_sdiff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).1).1

/-- **An unbound dart faces a selected region, has its own cell across, or neither.** -/
theorem card_unboundDarts_le (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (i : Fin S.diagram.rCellCount) :
    (RegionCandidate.unboundDarts S.family i).card ≤
      (S.toRealizedSectionFamily.regionFacingUnbound i).card + (sameCellUnbound S i).card +
        (otherCellOffRegions S i).card := by
  have hsub : RegionCandidate.unboundDarts S.family i ⊆
      (S.toRealizedSectionFamily.regionFacingUnbound i ∪ sameCellUnbound S i) ∪
        otherCellOffRegions S i := by
    intro d hd
    by_cases hreg : ∃ a ∈ S.family,
        S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∈ a.1
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hd, hreg⟩))
    · by_cases hsame :
          (cell S.diagram i).face = S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d)
      · exact Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hd, hsame⟩))
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hd, hreg⟩, hsame⟩)
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))

/-- The darts of the end loops of the selected regions. -/
noncomputable def regionEndDarts (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (regionEnd : RegionCandidate D eps S.diagram → Fin 4 → List S.diagram.toCombMap.Dart) :
    Finset S.diagram.toCombMap.Dart :=
  S.family.biUnion fun a => Finset.univ.biUnion fun t => (regionEnd a t).toFinset

/-- **The end loops of the selected regions carry at most `4 |M| B` darts.** -/
theorem card_regionEndDarts_le (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    {B : ℕ} (regionEnd : RegionCandidate D eps S.diagram → Fin 4 → List S.diagram.toCombMap.Dart)
    (hregionEnd : ∀ a ∈ S.family, ∀ t, (regionEnd a t).length ≤ B) :
    (regionEndDarts S regionEnd).card ≤ S.family.card * (4 * B) := by
  have hone : ∀ a ∈ S.family,
      (Finset.univ.biUnion fun t => (regionEnd a t).toFinset).card ≤ 4 * B := by
    intro a ha
    refine Finset.card_biUnion_le.trans ?_
    calc _ ≤ ∑ _t : Fin 4, B :=
          Finset.sum_le_sum fun t _ => (List.toFinset_card_le _).trans (hregionEnd a ha t)
      _ = 4 * B := by simp
  unfold regionEndDarts
  calc _ ≤ ∑ _a ∈ S.family, 4 * B := Finset.card_biUnion_le.trans (Finset.sum_le_sum hone)
    _ = S.family.card * (4 * B) := by simp

/-- The darts of the (A1) classes of the polygons with at least two classes. -/
noncomputable def relatorClassDarts
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    {P : OsinLemma94RealizedPolygons S} (Q : OsinLemma94ClassPolygons P) :
    Finset S.diagram.toCombMap.Dart :=
  Finset.univ.biUnion fun k => (Finset.range (Q.classCount k)).biUnion fun i =>
    if i ∈ Q.relatorClasses k then (Q.classDarts k i).toFinset else ∅

/-- **The (A1) classes carry at most `∑ S_i` darts.** -/
theorem card_relatorClassDarts_le
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    {P : OsinLemma94RealizedPolygons S} (Q : OsinLemma94ClassPolygons P) :
    ((relatorClassDarts Q).card : ℝ) ≤
      ∑ k, classWordLength (Q.word k) (Q.classCount k) (Q.relatorClasses k) := by
  have h : (relatorClassDarts Q).card ≤ ∑ k, ∑ i ∈ Finset.range (Q.classCount k),
      (if i ∈ Q.relatorClasses k then (Q.classDarts k i).toFinset else ∅).card := by
    unfold relatorClassDarts
    refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun k _ => ?_)
    exact Finset.card_biUnion_le
  refine le_trans (Nat.cast_le.mpr h) ?_
  rw [Nat.cast_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [Nat.cast_sum, classWordLength]
  refine Finset.sum_le_sum fun i _ => ?_
  split_ifs
  · simp only [OsinLemma94ClassPolygons.word, dartWord, List.length_map]
    exact_mod_cast List.toFinset_card_le (l := Q.classDarts k i)
  · simp

/-- The darts of the end loops of the classes of the budget polygons. -/
noncomputable def classEndDarts
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    {P : OsinLemma94RealizedPolygons S} (Q : OsinLemma94ClassPolygons P)
    (classEnd : Fin P.count → ℕ → Bool → List S.diagram.toCombMap.Dart) :
    Finset S.diagram.toCombMap.Dart :=
  Q.budgetPolygons.biUnion fun k => (Finset.range (Q.classCount k)).biUnion fun i =>
    Finset.univ.biUnion fun b => (classEnd k i b).toFinset

/-- **The end loops of the classes carry at most `2 K n B` darts.** -/
theorem card_classEndDarts_le
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    {P : OsinLemma94RealizedPolygons S} (Q : OsinLemma94ClassPolygons P) {K B : ℕ}
    (hbudget : Q.ClassBudget K)
    (classEnd : Fin P.count → ℕ → Bool → List S.diagram.toCombMap.Dart)
    (hclassEnd : ∀ k ∈ Q.budgetPolygons, ∀ i < Q.classCount k, ∀ b,
      (classEnd k i b).length ≤ B) :
    (classEndDarts Q classEnd).card ≤ 2 * B * (K * Delta.rCellCount) := by
  have hone : ∀ k ∈ Q.budgetPolygons, ((Finset.range (Q.classCount k)).biUnion fun i =>
      Finset.univ.biUnion fun b => (classEnd k i b).toFinset).card ≤
        Q.classCount k * (2 * B) := by
    intro k hk
    refine Finset.card_biUnion_le.trans ?_
    calc _ ≤ ∑ _i ∈ Finset.range (Q.classCount k), 2 * B := by
          refine Finset.sum_le_sum fun i hi => Finset.card_biUnion_le.trans ?_
          calc _ ≤ ∑ _b : Bool, B := Finset.sum_le_sum fun b _ =>
                (List.toFinset_card_le _).trans (hclassEnd k hk i (Finset.mem_range.mp hi) b)
            _ = 2 * B := by simp
      _ = Q.classCount k * (2 * B) := by simp
  have hsum : ∑ k ∈ Q.budgetPolygons, Q.classCount k ≤ K * Delta.rCellCount := hbudget
  unfold classEndDarts
  calc _ ≤ ∑ k ∈ Q.budgetPolygons, Q.classCount k * (2 * B) :=
        Finset.card_biUnion_le.trans (Finset.sum_le_sum hone)
    _ = (∑ k ∈ Q.budgetPolygons, Q.classCount k) * (2 * B) := by rw [Finset.sum_mul]
    _ ≤ K * Delta.rCellCount * (2 * B) := Nat.mul_le_mul hsum le_rfl
    _ = 2 * B * (K * Delta.rCellCount) := by ring

end OsinLemma94ClassCovers

namespace OsinLemma94ClassPolygons

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
  {P : OsinLemma94RealizedPolygons S}

/-- The darts of a side lie in the darts of its class. -/
theorem mem_classDarts_of_mem_sideDarts (Q : OsinLemma94ClassPolygons P) {k : Fin P.count}
    {i s : ℕ} (hs : s ∈ Q.classSides k i) {d : S.diagram.toCombMap.Dart}
    (hd : d ∈ P.sideDarts k s) : d ∈ Q.classDarts k i := by
  unfold classDarts
  exact List.mem_flatMap.mpr ⟨s, hs, List.mem_append_left _ hd⟩

/-- **An (A1) side lies in an (A1) class.** -/
theorem exists_class_of_relatorSide (Q : OsinLemma94ClassPolygons P) {k : Fin P.count} {s : ℕ}
    (hs : s < P.sideCount k) (hrel : s ∈ P.relatorSides k) :
    ∃ i < Q.classCount k, s ∈ Q.classSides k i ∧ ∃ j, Q.classKind k i = .cell j := by
  have hmem : s ∈ (List.range (Q.classCount k)).flatMap (Q.classSides k) := by
    rw [Q.sides_eq k, List.mem_rotate]
    exact List.mem_range.mpr hs
  obtain ⟨i, hi, hsi⟩ := List.mem_flatMap.mp hmem
  obtain ⟨j, hj⟩ : ∃ j, P.kind k s = .cell j := hrel
  exact ⟨i, List.mem_range.mp hi, hsi, j,
    (Q.kind_eq k i (List.mem_range.mp hi) s hsi).symm.trans hj⟩

/-- **The class cover from the end loops.**  Suppose at most `T n` unbound darts have their own
cell across, every other unbound dart facing no selected region lies across an (A1) side, and
the reverse of such a dart on a polygon with a single class lies in an (A1) class of a polygon
with at least two classes or in an end loop.  If there are at most two end loops per class of a
budget polygon and four per selected region, each with at most `B` darts, then the class
polygons cover the unbound darts with slack `24 ε + 2 (K + 24) B + T`. -/
theorem classCovers_of_endLoops (Q : OsinLemma94ClassPolygons P)
    (hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1)
    (hcells : 0 < Delta.rCellCount)
    (hcard : S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1))
    {K B T : ℕ} (hbudget : Q.ClassBudget K)
    (hsameCell : ∑ i : Fin S.diagram.rCellCount,
      ((RegionCandidate.unboundDarts S.family i).filter fun d =>
        (cell S.diagram i).face =
          S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d)).card ≤
        T * Delta.rCellCount)
    (hside : ∀ (i : Fin S.diagram.rCellCount) (d : S.diagram.toCombMap.Dart),
      d ∈ S.unboundOffRegions i →
        (cell S.diagram i).face ≠ S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) →
          ∃ k s, s < P.sideCount k ∧ s ∈ P.relatorSides k ∧
            S.diagram.toCombMap.alpha d ∈ P.sideDarts k s)
    (classEnd : Fin P.count → ℕ → Bool → List S.diagram.toCombMap.Dart)
    (regionEnd : RegionCandidate D eps S.diagram → Fin 4 → List S.diagram.toCombMap.Dart)
    (hclassEnd : ∀ k ∈ Q.budgetPolygons, ∀ i < Q.classCount k, ∀ b,
      (classEnd k i b).length ≤ B)
    (hregionEnd : ∀ a ∈ S.family, ∀ t, (regionEnd a t).length ≤ B)
    (hbubble : ∀ (i : Fin S.diagram.rCellCount) (d : S.diagram.toCombMap.Dart),
      d ∈ S.unboundOffRegions i →
        (cell S.diagram i).face ≠ S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) →
          ∀ k s, Q.classCount k = 1 → s < P.sideCount k → s ∈ P.relatorSides k →
            S.diagram.toCombMap.alpha d ∈ P.sideDarts k s →
              (∃ k' i', i' < Q.classCount k' ∧ i' ∈ Q.relatorClasses k' ∧
                  S.diagram.toCombMap.alpha d ∈ Q.classDarts k' i') ∨
                (∃ k' ∈ Q.budgetPolygons, ∃ i' < Q.classCount k', ∃ b,
                  S.diagram.toCombMap.alpha d ∈ classEnd k' i' b) ∨
                ∃ a ∈ S.family, ∃ t, S.diagram.toCombMap.alpha d ∈ regionEnd a t) :
    Q.ClassCovers (24 * eps + 2 * (K + 24) * B + T) := by
  have hfam : S.family.card ≤ 12 * Delta.rCellCount := by
    have := cuts.count_le
    omega
  have hsum : (∑ i : Fin S.diagram.rCellCount,
      ((RegionCandidate.unboundDarts S.family i).card : ℝ)) ≤
      (∑ i : Fin S.diagram.rCellCount,
          ((S.toRealizedSectionFamily.regionFacingUnbound i).card : ℝ)) +
        (∑ i : Fin S.diagram.rCellCount,
          ((OsinLemma94ClassCovers.sameCellUnbound S i).card : ℝ)) +
          ∑ i : Fin S.diagram.rCellCount,
            ((OsinLemma94ClassCovers.otherCellOffRegions S i).card : ℝ) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    exact_mod_cast OsinLemma94ClassCovers.card_unboundDarts_le S i
  have hregion : (∑ i : Fin S.diagram.rCellCount,
      ((S.toRealizedSectionFamily.regionFacingUnbound i).card : ℝ)) ≤
        24 * eps * Delta.rCellCount := by
    have h : ∑ i : Fin S.diagram.rCellCount,
        (S.toRealizedSectionFamily.regionFacingUnbound i).card ≤ 24 * eps * Delta.rCellCount :=
      calc _ ≤ 2 * eps * S.family.card :=
            S.toRealizedSectionFamily.sum_card_regionFacingUnbound_le hvalue
        _ ≤ 2 * eps * (12 * Delta.rCellCount) := Nat.mul_le_mul le_rfl hfam
        _ = 24 * eps * Delta.rCellCount := by ring
    exact_mod_cast h
  have hsame : (∑ i : Fin S.diagram.rCellCount,
      ((OsinLemma94ClassCovers.sameCellUnbound S i).card : ℝ)) ≤ T * Delta.rCellCount := by
    have h : ∑ i : Fin S.diagram.rCellCount, (OsinLemma94ClassCovers.sameCellUnbound S i).card ≤
        T * Delta.rCellCount := hsameCell
    exact_mod_cast h
  have hmem : ∀ (i : Fin S.diagram.rCellCount) (d : S.diagram.toCombMap.Dart),
      d ∈ OsinLemma94ClassCovers.otherCellOffRegions S i → d ∈ cellDarts S.diagram i :=
    fun _ _ hd => OsinLemma94ClassCovers.mem_cellDarts_of_mem_otherCellOffRegions S hd
  have hdisj : ((Finset.univ : Finset (Fin S.diagram.rCellCount)) :
      Set (Fin S.diagram.rCellCount)).PairwiseDisjoint
        (OsinLemma94ClassCovers.otherCellOffRegions S) := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun d hdi hdj => hij (cell_face_injective S.diagram ?_)
    exact (faceOf_of_mem_cellDarts (hmem i d hdi)).symm.trans
      (faceOf_of_mem_cellDarts (hmem j d hdj))
  have hmaps : Set.MapsTo S.diagram.toCombMap.alpha
      (Finset.univ.biUnion (OsinLemma94ClassCovers.otherCellOffRegions S) :
        Set S.diagram.toCombMap.Dart)
      (((OsinLemma94ClassCovers.relatorClassDarts Q ∪
          OsinLemma94ClassCovers.classEndDarts Q classEnd) ∪
        OsinLemma94ClassCovers.regionEndDarts S regionEnd : Finset S.diagram.toCombMap.Dart) :
          Set S.diagram.toCombMap.Dart) := by
    intro d hd
    obtain ⟨i, -, hdi⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hd)
    obtain ⟨hoff, hne⟩ := Finset.mem_filter.mp hdi
    obtain ⟨k, s, hs, hrel, hds⟩ := hside i d hoff hne
    obtain ⟨i', hi', hsi', j, hj⟩ := Q.exists_class_of_relatorSide hs hrel
    refine Finset.mem_coe.mpr ?_
    by_cases h2 : 2 ≤ Q.classCount k
    · refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
      refine Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _,
        Finset.mem_biUnion.mpr ⟨i', Finset.mem_range.mpr hi', ?_⟩⟩
      rw [if_pos (show i' ∈ Q.relatorClasses k from ⟨h2, j, hj⟩)]
      exact List.mem_toFinset.mpr (Q.mem_classDarts_of_mem_sideDarts hsi' hds)
    · have h1 : Q.classCount k = 1 := by omega
      rcases hbubble i d hoff hne k s h1 hs hrel hds with
        ⟨k', i'', hi'', hrel', hd'⟩ | ⟨k', hk', i'', hi'', b, hd'⟩ | ⟨a, ha, t, hd'⟩
      · refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
        refine Finset.mem_biUnion.mpr ⟨k', Finset.mem_univ _,
          Finset.mem_biUnion.mpr ⟨i'', Finset.mem_range.mpr hi'', ?_⟩⟩
        rw [if_pos hrel']
        exact List.mem_toFinset.mpr hd'
      · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
        exact Finset.mem_biUnion.mpr ⟨k', hk', Finset.mem_biUnion.mpr
          ⟨i'', Finset.mem_range.mpr hi'',
            Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ _, List.mem_toFinset.mpr hd'⟩⟩⟩
      · refine Finset.mem_union_right _ ?_
        exact Finset.mem_biUnion.mpr ⟨a, ha,
          Finset.mem_biUnion.mpr ⟨t, Finset.mem_univ _, List.mem_toFinset.mpr hd'⟩⟩
  have hcardOff := Finset.card_le_card_of_injOn S.diagram.toCombMap.alpha hmaps
    S.diagram.toCombMap.alpha_involutive.injective.injOn
  rw [Finset.card_biUnion hdisj] at hcardOff
  have hoff : (∑ i : Fin S.diagram.rCellCount,
      ((OsinLemma94ClassCovers.otherCellOffRegions S i).card : ℝ)) ≤
        ((OsinLemma94ClassCovers.relatorClassDarts Q).card : ℝ) +
          ((OsinLemma94ClassCovers.classEndDarts Q classEnd).card : ℝ) +
            ((OsinLemma94ClassCovers.regionEndDarts S regionEnd).card : ℝ) := by
    exact_mod_cast hcardOff.trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hclass : ((OsinLemma94ClassCovers.classEndDarts Q classEnd).card : ℝ) ≤
      2 * B * (K * Delta.rCellCount) := by
    exact_mod_cast OsinLemma94ClassCovers.card_classEndDarts_le Q hbudget classEnd hclassEnd
  have hregionEnd' : ((OsinLemma94ClassCovers.regionEndDarts S regionEnd).card : ℝ) ≤
      12 * Delta.rCellCount * (4 * B) := by
    exact_mod_cast (OsinLemma94ClassCovers.card_regionEndDarts_le S regionEnd hregionEnd).trans
      (Nat.mul_le_mul_right _ hfam)
  have hrel := OsinLemma94ClassCovers.card_relatorClassDarts_le Q
  unfold ClassCovers
  push_cast
  linarith

end OsinLemma94ClassPolygons

#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94ClassCovers.mem_cellDarts_of_mem_otherCellOffRegions
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94ClassCovers.card_unboundDarts_le
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94ClassCovers.card_regionEndDarts_le
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94ClassCovers.card_relatorClassDarts_le
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94ClassCovers.card_classEndDarts_le
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94ClassPolygons.mem_classDarts_of_mem_sideDarts
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94ClassPolygons.exists_class_of_relatorSide
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94ClassPolygons.classCovers_of_endLoops

end GroupApproximation.GGT.VanKampen
