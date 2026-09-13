import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PolygonClasses
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PolygonCovers
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94RegionSideCount
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassCoversSameCellFactor
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.4: the other-facing unbound darts from the end loops

Osin (math/0411039v3, §9), proof of Lemma 9.4: "Let `S_i` denote the sum of lengths of all arcs
of type (A1) in `∂Δ_i`, `i = 1, …, d`. [...] Indeed otherwise we have
`S = ∑_{i=1}^d S_i ≤ (√ρ / 60) ∑_{i=1}^d n_i < n √ρ`."

This module bounds the unbound darts whose reverse lies on a different face by the (A1) class
words, up to `(24 ε + 2 (K + 24) B) n`.  That is hypothesis (i) of
`OsinLemma94ClassPolygons.classCovers_of_sameCellFactor`.  The count follows hull-component's
`classCovers_of_endLoops` (13cf15e1a) with its same-cell hypothesis removed.  The unbound darts
with their own cell across are not bounded here: along an unbound stretch they are bounded only
by a factor on the other unbound darts, so a bound `T n` is not available.

* `OsinLemma94OtherFacingCover.card_otherFacing_le`: an other-facing unbound dart faces a selected
  region, or faces no selected region and no cell of its own.
* `OsinLemma94OtherFacingCover.otherFacingCover_of_endLoops`: hypothesis (i).  The darts facing a
  selected region number at most `24 ε n`.  The reverses of the others lie in an (A1) class of a
  polygon with at least two classes, or in an end loop, which carry at most
  `∑ S_i + 2 K n B + 4 |M| B` darts.
* `OsinLemma94OtherFacingCover.classCovers_of_endLoops_sameCellFactor`: the class cover
  `ClassCovers (M₀ + 1) ((M₀ + 1) (24 ε + 2 (K + 24) B) + T)`, given the same-cell factor bound.

## Manuscript status

Infrastructure for `thm:hull` ("Hull's small cancellation theorem", through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open scoped Classical

namespace OsinLemma94OtherFacingCover

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

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

/-- **An other-facing unbound dart faces a selected region, or neither a region nor its cell.** -/
theorem card_otherFacing_le (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (i : Fin S.diagram.rCellCount) :
    ((RegionCandidate.unboundDarts S.family i).filter fun d =>
        ¬ (cell S.diagram i).face =
          S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d)).card ≤
      (S.toRealizedSectionFamily.regionFacingUnbound i).card + (otherCellOffRegions S i).card := by
  have hsub : ((RegionCandidate.unboundDarts S.family i).filter fun d =>
        ¬ (cell S.diagram i).face =
          S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d)) ⊆
      S.toRealizedSectionFamily.regionFacingUnbound i ∪ otherCellOffRegions S i := by
    intro d hdf
    obtain ⟨hunb, hne⟩ := Finset.mem_filter.mp hdf
    by_cases hreg : ∃ a ∈ S.family,
        S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∈ a.1
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hunb, hreg⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hunb, hreg⟩, hne⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

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

variable {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
  {P : OsinLemma94RealizedPolygons S}

/-- The darts of a side lie in the darts of its class. -/
theorem mem_classDarts_of_mem_sideDarts (Q : OsinLemma94ClassPolygons P) {k : Fin P.count}
    {i s : ℕ} (hs : s ∈ Q.classSides k i) {d : S.diagram.toCombMap.Dart}
    (hd : d ∈ P.sideDarts k s) : d ∈ Q.classDarts k i := by
  unfold OsinLemma94ClassPolygons.classDarts
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

/-- **Hypothesis (i) of the same-cell factor cover, from the end loops.**  Suppose every
unbound dart facing no selected region and not its own cell lies across an (A1) side, and the
reverse of such a dart on a polygon with a single class lies in an (A1) class of a polygon with
at least two classes or in an end loop.  If there are at most two end loops per class of a budget
polygon and four per selected region, each with at most `B` darts, then the unbound darts whose
reverse lies on a different face number at most `∑ S_i + (24 ε + 2 (K + 24) B) n`. -/
theorem otherFacingCover_of_endLoops (Q : OsinLemma94ClassPolygons P)
    (hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1)
    (hcells : 0 < Delta.rCellCount)
    (hcard : S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1))
    {K B : ℕ} (hbudget : Q.ClassBudget K)
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
    (∑ i : Fin S.diagram.rCellCount,
        (((RegionCandidate.unboundDarts S.family i).filter fun d =>
          ¬ (cell S.diagram i).face =
            S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d)).card : ℝ)) ≤
      ∑ k, classWordLength (Q.word k) (Q.classCount k) (Q.relatorClasses k) +
        ((24 * eps + 2 * (K + 24) * B : ℕ) : ℝ) * Delta.rCellCount := by
  have hfam : S.family.card ≤ 12 * Delta.rCellCount := by
    have := cuts.count_le
    omega
  have hsum : (∑ i : Fin S.diagram.rCellCount,
      (((RegionCandidate.unboundDarts S.family i).filter fun d =>
        ¬ (cell S.diagram i).face =
          S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d)).card : ℝ)) ≤
      (∑ i : Fin S.diagram.rCellCount,
          ((S.toRealizedSectionFamily.regionFacingUnbound i).card : ℝ)) +
        ∑ i : Fin S.diagram.rCellCount, ((otherCellOffRegions S i).card : ℝ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    exact_mod_cast card_otherFacing_le S i
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
  have hmem : ∀ (i : Fin S.diagram.rCellCount) (d : S.diagram.toCombMap.Dart),
      d ∈ otherCellOffRegions S i → d ∈ cellDarts S.diagram i :=
    fun _ _ hd => mem_cellDarts_of_mem_otherCellOffRegions S hd
  have hdisj : ((Finset.univ : Finset (Fin S.diagram.rCellCount)) :
      Set (Fin S.diagram.rCellCount)).PairwiseDisjoint (otherCellOffRegions S) := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun d hdi hdj => hij (cell_face_injective S.diagram ?_)
    exact (faceOf_of_mem_cellDarts (hmem i d hdi)).symm.trans
      (faceOf_of_mem_cellDarts (hmem j d hdj))
  have hmaps : Set.MapsTo S.diagram.toCombMap.alpha
      (Finset.univ.biUnion (otherCellOffRegions S) : Set S.diagram.toCombMap.Dart)
      (((relatorClassDarts Q ∪ classEndDarts Q classEnd) ∪
        regionEndDarts S regionEnd : Finset S.diagram.toCombMap.Dart) :
          Set S.diagram.toCombMap.Dart) := by
    intro d hd
    obtain ⟨i, -, hdi⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hd)
    obtain ⟨hoff, hne⟩ := Finset.mem_filter.mp hdi
    obtain ⟨k, s, hs, hrel, hds⟩ := hside i d hoff hne
    obtain ⟨i', hi', hsi', j, hj⟩ := exists_class_of_relatorSide Q hs hrel
    refine Finset.mem_coe.mpr ?_
    by_cases h2 : 2 ≤ Q.classCount k
    · refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
      refine Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _,
        Finset.mem_biUnion.mpr ⟨i', Finset.mem_range.mpr hi', ?_⟩⟩
      rw [if_pos (show i' ∈ Q.relatorClasses k from ⟨h2, j, hj⟩)]
      exact List.mem_toFinset.mpr (mem_classDarts_of_mem_sideDarts Q hsi' hds)
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
  have hoff : (∑ i : Fin S.diagram.rCellCount, ((otherCellOffRegions S i).card : ℝ)) ≤
      ((relatorClassDarts Q).card : ℝ) + ((classEndDarts Q classEnd).card : ℝ) +
        ((regionEndDarts S regionEnd).card : ℝ) := by
    exact_mod_cast hcardOff.trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hclass : ((classEndDarts Q classEnd).card : ℝ) ≤ 2 * B * (K * Delta.rCellCount) := by
    exact_mod_cast card_classEndDarts_le Q hbudget classEnd hclassEnd
  have hregionEnd' : ((regionEndDarts S regionEnd).card : ℝ) ≤
      12 * Delta.rCellCount * (4 * B) := by
    exact_mod_cast (card_regionEndDarts_le S regionEnd hregionEnd).trans
      (Nat.mul_le_mul_right _ hfam)
  have hrel := card_relatorClassDarts_le Q
  push_cast
  linarith

/-- **The class cover from the end loops and the same-cell factor.**  With the end-loop
hypotheses of `otherFacingCover_of_endLoops`, and the unbound darts with their own cell across
numbering at most `M₀` times the other unbound darts plus `T n`, the class polygons cover every
unbound dart with factor `M₀ + 1` and slack `(M₀ + 1) (24 ε + 2 (K + 24) B) + T`. -/
theorem classCovers_of_endLoops_sameCellFactor (Q : OsinLemma94ClassPolygons P)
    (hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1)
    (hcells : 0 < Delta.rCellCount)
    (hcard : S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1))
    {K B M₀ T : ℕ} (hbudget : Q.ClassBudget K)
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
                ∃ a ∈ S.family, ∃ t, S.diagram.toCombMap.alpha d ∈ regionEnd a t)
    (hsame : (∑ i : Fin S.diagram.rCellCount,
        (((RegionCandidate.unboundDarts S.family i).filter fun d =>
          (cell S.diagram i).face =
            S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d)).card : ℝ)) ≤
      (M₀ : ℝ) * (∑ i : Fin S.diagram.rCellCount,
        (((RegionCandidate.unboundDarts S.family i).filter fun d =>
          ¬ (cell S.diagram i).face =
            S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d)).card : ℝ)) +
        (T : ℝ) * Delta.rCellCount) :
    Q.ClassCovers (M₀ + 1) ((M₀ + 1) * (24 * eps + 2 * (K + 24) * B) + T) :=
  Q.classCovers_of_sameCellFactor
    (otherFacingCover_of_endLoops Q hvalue hcells hcard hbudget hside classEnd regionEnd
      hclassEnd hregionEnd hbubble) hsame

end OsinLemma94OtherFacingCover

#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94OtherFacingCover.mem_cellDarts_of_mem_otherCellOffRegions
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94OtherFacingCover.card_otherFacing_le
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94OtherFacingCover.card_regionEndDarts_le
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94OtherFacingCover.card_relatorClassDarts_le
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94OtherFacingCover.card_classEndDarts_le
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94OtherFacingCover.mem_classDarts_of_mem_sideDarts
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94OtherFacingCover.exists_class_of_relatorSide
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94OtherFacingCover.otherFacingCover_of_endLoops
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94OtherFacingCover.classCovers_of_endLoops_sameCellFactor

end GroupApproximation.GGT.VanKampen
