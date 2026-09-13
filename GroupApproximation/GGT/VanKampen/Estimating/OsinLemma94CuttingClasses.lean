import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94CuttingSidesCount
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PolygonClasses
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassRuns
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.4, (38): the cutting classes of a polygon

Osin (math/0411039v3, §9), proof of Lemma 9.4, (38): "`k_i ≤ 4 n_i`".  The class budget
`OsinLemma94ClassPolygons.ClassBudget` counts classes.  Cutting classes are single sides, and
nothing on the side of Lemma 9.3 counts them.  This module bounds them by the other classes,
through the side count `OsinLemma94RealizedPolygons.card_cuttingSides_le`.

* `cuttingClasses`, `otherClasses`: the cutting classes of polygon `k`, and the others.
* `card_cuttingClasses_le`: different classes start with different sides, so there are at most
  as many cutting classes as cutting sides.
* `mem_getLast?_of_next_kind_ne`: classes are runs of consecutive sides, so a side whose next side
  has another kind ends its class.
* `card_cuttingEntries_le`: the side before an entry ends a class that is not a cutting class,
  so there are at most as many entries as other classes.
* `card_cuttingClasses_le_otherClasses`: `#cutting classes ≤ 4 · #other classes + 1`, over the
  forest property.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121 at origin/main 68481e4d7, through Osin's Lemma 9.4 inside
the proof of Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

namespace OsinLemma94ClassPolygons

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
  {P : OsinLemma94RealizedPolygons S}

open Classical in
/-- The cutting classes of polygon `k`. -/
noncomputable def cuttingClasses (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) :
    Finset ℕ :=
  (Finset.range (Q.classCount k)).filter fun i => Q.classKind k i = .cutting

open Classical in
/-- The classes of polygon `k` that are not cutting classes. -/
noncomputable def otherClasses (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) :
    Finset ℕ :=
  (Finset.range (Q.classCount k)).filter fun i => Q.classKind k i ≠ .cutting

open Classical in
theorem mem_cuttingClasses (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) (i : ℕ) :
    i ∈ Q.cuttingClasses k ↔ i < Q.classCount k ∧ Q.classKind k i = .cutting := by
  unfold cuttingClasses
  rw [Finset.mem_filter, Finset.mem_range]

open Classical in
theorem mem_otherClasses (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) (i : ℕ) :
    i ∈ Q.otherClasses k ↔ i < Q.classCount k ∧ Q.classKind k i ≠ .cutting := by
  unfold otherClasses
  rw [Finset.mem_filter, Finset.mem_range]

/-- The side after the side before `s` is `s`. -/
theorem add_one_mod_pred_eq {n s : ℕ} (hs : s < n) : ((s + n - 1) % n + 1) % n = s := by
  rcases Nat.eq_zero_or_pos s with rfl | hpos
  · rw [show 0 + n - 1 = n - 1 by omega, Nat.mod_eq_of_lt (show n - 1 < n by omega),
      show n - 1 + 1 = n by omega, Nat.mod_self]
  · rw [show s + n - 1 = s - 1 + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (show s - 1 < n by omega), show s - 1 + 1 = s by omega,
      Nat.mod_eq_of_lt hs]

/-- Every side of the polygon lies in a class. -/
theorem exists_class_of_side (Q : OsinLemma94ClassPolygons P) {k : Fin P.count} {s : ℕ}
    (hs : s < P.sideCount k) : ∃ i < Q.classCount k, s ∈ Q.classSides k i := by
  have hmem : s ∈ (List.range (Q.classCount k)).flatMap (Q.classSides k) := by
    rw [Q.sides_eq k, List.mem_rotate]
    exact List.mem_range.mpr hs
  obtain ⟨i, hi, hsi⟩ := List.mem_flatMap.mp hmem
  exact ⟨i, List.mem_range.mp hi, hsi⟩

/-- Two different classes of one polygon have no common side. -/
theorem classSides_disjoint (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) {i j : ℕ}
    (hi : i < Q.classCount k) (hj : j < Q.classCount k) (hij : i ≠ j) :
    List.Disjoint (Q.classSides k i) (Q.classSides k j) := by
  have hnodup : ((List.range (Q.classCount k)).flatMap (Q.classSides k)).Nodup := by
    rw [Q.sides_eq k]
    exact List.nodup_rotate.mpr List.nodup_range
  have hpair := List.pairwise_iff_getElem.mp (List.nodup_flatMap.mp hnodup).2
  have key : ∀ a b, a < b → b < Q.classCount k →
      List.Disjoint (Q.classSides k a) (Q.classSides k b) := by
    intro a b hab hb
    have h := hpair a b (by rw [List.length_range]; omega) (by rw [List.length_range]; omega)
      hab
    simpa only [Function.onFun, List.getElem_range] using h
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact key i j h hj
  · exact (key j i h hi).symm

/-- **A class ends where the kind changes.**  The classes are runs of consecutive sides, so if
side `p` lies in class `i` and the next side `(p + 1) % n` has another kind, then `p` is the last
side of class `i`. -/
theorem mem_getLast?_of_next_kind_ne (Q : OsinLemma94ClassPolygons P) {k : Fin P.count}
    {i p : ℕ} (hi : i < Q.classCount k) (hp : p ∈ Q.classSides k i)
    (hnext : P.kind k ((p + 1) % P.sideCount k) ≠ Q.classKind k i) :
    p ∈ (Q.classSides k i).getLast? := by
  obtain ⟨s, t, hst⟩ := List.append_of_mem hp
  cases t with
  | nil =>
    rw [hst]
    simp
  | cons q B =>
    exfalso
    have hinf : Q.classSides k i <:+: (List.range (P.sideCount k)).rotate (Q.classBase k) := by
      rw [← Q.sides_eq k, OsinLemma94RealizedPolygons.range_flatMap_eq_split (Q.classSides k) hi]
      exact ⟨_, _, rfl⟩
    have hchain := (CyclicRuns.isChain_rotate_range (P.sideCount k) (Q.classBase k)).infix hinf
    rw [hst] at hchain
    have hpq : q = (p + 1) % P.sideCount k :=
      (List.isChain_cons_cons.mp hchain.right_of_append).1
    have hq : q ∈ Q.classSides k i := by
      rw [hst]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    apply hnext
    rw [← hpq]
    exact Q.kind_eq k i hi q hq

/-- **Cutting classes against cutting sides.**  A cutting class starts with a cutting side, and
different classes start with different sides. -/
theorem card_cuttingClasses_le (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) :
    (Q.cuttingClasses k).card ≤ (P.cuttingSides k).card := by
  have hhead : ∀ i, i < Q.classCount k → (Q.classSides k i).headD 0 ∈ Q.classSides k i := by
    intro i hi
    obtain ⟨a, l, hal⟩ := List.exists_cons_of_ne_nil (Q.classSides_ne_nil k i hi)
    rw [hal]
    exact List.mem_cons_self ..
  refine Finset.card_le_card_of_injOn (fun i => (Q.classSides k i).headD 0) ?_ ?_
  · intro i hi
    obtain ⟨hic, hkind⟩ := (Q.mem_cuttingClasses k i).mp (Finset.mem_coe.mp hi)
    have hmem := hhead i hic
    refine Finset.mem_coe.mpr ((P.mem_cuttingSides k _).mpr
      ⟨Q.lt_sideCount_of_mem k i hic _ hmem, ?_⟩)
    exact (Q.kind_eq k i hic _ hmem).trans hkind
  · intro i hi j hj hij
    have hic := ((Q.mem_cuttingClasses k i).mp (Finset.mem_coe.mp hi)).1
    have hjc := ((Q.mem_cuttingClasses k j).mp (Finset.mem_coe.mp hj)).1
    have heq : (Q.classSides k i).headD 0 = (Q.classSides k j).headD 0 := hij
    have hmi := hhead i hic
    have hmj := hhead j hjc
    rw [← heq] at hmj
    by_contra hne
    exact Q.classSides_disjoint k hic hjc hne hmi hmj

/-- **Entries against other classes.**  The side before an entry is not a cutting side and the
entry is, so the side before it ends its class, which is not a cutting class.  Different entries
give different classes. -/
theorem card_cuttingEntries_le (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) :
    (P.cuttingEntries k).card ≤ (Q.otherClasses k).card := by
  have hsub : P.cuttingEntries k ⊆ (Q.otherClasses k).image
      fun i => (((Q.classSides k i).getLast?).getD 0 + 1) % P.sideCount k := by
    intro s hs
    obtain ⟨⟨hsn, hscut⟩, hpred⟩ := (P.mem_cuttingEntries k s).mp hs
    have hp : (s + P.sideCount k - 1) % P.sideCount k < P.sideCount k :=
      Nat.mod_lt _ (by omega)
    obtain ⟨i, hi, hpi⟩ := Q.exists_class_of_side hp
    have hkind := Q.kind_eq k i hi _ hpi
    have hlast := Q.mem_getLast?_of_next_kind_ne hi hpi (by
      rw [add_one_mod_pred_eq hsn, hscut, ← hkind]
      exact fun h => hpred h.symm)
    refine Finset.mem_image.mpr ⟨i, (Q.mem_otherClasses k i).mpr ⟨hi, ?_⟩, ?_⟩
    · rw [← hkind]
      exact hpred
    · show (((Q.classSides k i).getLast?).getD 0 + 1) % P.sideCount k = s
      rw [Option.mem_def.mp hlast]
      exact add_one_mod_pred_eq hsn
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-- **(38), the cutting classes.**  For a dart-minimal family with maximal sides, polygon `k` has
at most `4 m + 1` cutting classes, where `m` is its number of other classes. -/
theorem card_cuttingClasses_le_otherClasses (hforest : SameFaceDartForestStatement.{v})
    (hS : S.DartMinimal) (hmax : P.Maximal) (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) :
    (Q.cuttingClasses k).card ≤ 4 * (Q.otherClasses k).card + 1 := by
  have h1 := Q.card_cuttingClasses_le k
  have h2 := P.card_cuttingSides_le hforest hS hmax k
  have h3 := Q.card_cuttingEntries_le k
  omega

end OsinLemma94ClassPolygons

/-- **(38), the cutting classes.**  Osin, proof of Lemma 9.4, (38): "`k_i ≤ 4 n_i`".  For a
dart-minimal family with maximal sides and any class polygons, polygon `k` has at most `4 m + 1`
cutting classes, where `m` counts its classes of the other kinds. -/
def OsinLemma94CuttingClassesStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts), S.DartMinimal →
      ∀ P : OsinLemma94RealizedPolygons S, P.Maximal →
        ∀ (Q : OsinLemma94ClassPolygons P) (k : Fin P.count),
          (Q.cuttingClasses k).card ≤ 4 * (Q.otherClasses k).card + 1

/-- **(38), the cutting classes, from the forest property.** -/
theorem osinLemma94CuttingClasses_of_forest (hforest : SameFaceDartForestStatement.{v}) :
    OsinLemma94CuttingClassesStatement.{u, w, v} := by
  intro G _ Lambda W D lambda c eps Delta cuts S hS P hmax Q k
  exact Q.card_cuttingClasses_le_otherClasses hforest hS hmax k

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94ClassPolygons.mem_getLast?_of_next_kind_ne
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94ClassPolygons.card_cuttingClasses_le
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94ClassPolygons.card_cuttingEntries_le
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94ClassPolygons.card_cuttingClasses_le_otherClasses
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94CuttingClasses_of_forest
