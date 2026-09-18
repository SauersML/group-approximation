import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10WalkPetals.Pinch
import GroupApproximation.Meta.AxiomGuard

/-!
# A minimal petal is a simple closed walk inside `c`; what it shares with the rest of `c`

Lane gl-infra-01 (infrastructure).

* `infraPetal_isSimple`: if no dart of `c` has its reverse in `c` (true for a boundary cycle),
  every petal is a simple closed walk (`IsSimpleClosedWalk`) made of darts of `c`.
* `infraPetal_exists_min_petal`, `infraPetal_boundary_min_petal`: a petal of minimal length
  exists; it is a simple closed walk `B ⊆ c`.
* `infraPetal_onB_iff`: for a closed walk `B`, a vertex is on `B` iff it is a start vertex of a
  dart of `B`.
* `infraPetal_rest_meets`: **what `B` shares with the rest of `c`.**  A dart `d ∈ c` off `B` is
  not retained by `B` (neither `d` nor its reverse is on `B`: the rest meets `B` only at
  vertices, never along an edge), and if the start vertex of `d` is on `B` it is the start of a
  *different* dart of `c` (so it is a repeated start vertex of `c`).  Any vertex of `B` can be
  shared: nothing more is true in general.

## LOUD: the "untouched or one-sided" dichotomy for a minimal petal is FALSE

The claim "a minimal petal `B` is untouched away from one vertex (`p10QS_Untouched`) or all
darts of `c` off `B` lie on one side of `B`" fails.  Brute force (scratchpad
`gl-infra-01/petal.py`, seeds 5-7) finds boundary cycles made of three digons between two
vertices, vertex sequence `0,2,0,2,0,2` (e.g. `c = [17,11,19,9,22,5]`): every petal is a digon
sharing both of its vertices with the rest of `c`, with the rest on both sides.  By hand: a
triangle petal with a hole lobe inside it at `v1` and an outer lobe at `v2`.  Even with the
rose premises (seed 1) "every minimal petal is good" fails (2715 of 2721).  What is true, and
proved in `P10WalkPetals.Side`, is the one-sided criterion for a linear block whose
complementary excursion avoids `B` in its interior (`infraPetal_oneSided_of_block`).

All PROVED, unconditionally.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove

universe v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10FilterMoveExists

section Shared

/-- A nonempty list of lists has a member of minimal length. -/
theorem infraPetal_exists_min {α : Type*} (Ps : List (List α)) (hPs : Ps ≠ []) :
    ∃ B ∈ Ps, ∀ P ∈ Ps, B.length ≤ P.length := by
  induction Ps with
  | nil => exact (hPs rfl).elim
  | cons A Ps ih =>
    by_cases hnil : Ps = []
    · refine ⟨A, List.mem_cons_self, fun P hP => ?_⟩
      rw [hnil] at hP
      rcases List.mem_singleton.mp hP with rfl
      exact le_refl _
    · obtain ⟨B, hB, hmin⟩ := ih hnil
      by_cases hAB : A.length ≤ B.length
      · refine ⟨A, List.mem_cons_self, fun P hP => ?_⟩
        rcases List.mem_cons.mp hP with rfl | hP'
        · exact le_refl _
        · exact le_trans hAB (hmin P hP')
      · refine ⟨B, List.mem_cons_of_mem A hB, fun P hP => ?_⟩
        rcases List.mem_cons.mp hP with rfl | hP'
        · omega
        · exact hmin P hP'

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.infraPetal_exists_min

/-- A dart of a petal is a dart of `c`. -/
theorem infraPetal_mem {M : CombMap.{v}} {c : List M.Dart} {Ps : List (List M.Dart)}
    (hD : infraPetal_IsDecomp M c Ps) {P : List M.Dart} (hP : P ∈ Ps) {x : M.Dart}
    (hx : x ∈ P) : x ∈ c := by
  obtain ⟨-, hperm⟩ := hD
  exact hperm.mem_iff.mp (List.mem_flatten.mpr ⟨P, hP, hx⟩)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.infraPetal_mem

/-- **Petals are simple closed walks** when no dart of `c` has its reverse in `c`. -/
theorem infraPetal_isSimple {M : CombMap.{v}} {c : List M.Dart} {Ps : List (List M.Dart)}
    (hD : infraPetal_IsDecomp M c Ps) (halpha : ∀ d ∈ c, M.alpha d ∉ c) {P : List M.Dart}
    (hP : P ∈ Ps) : IsSimpleClosedWalk M P := by
  have hPc : ∀ x ∈ P, x ∈ c := fun x hx => infraPetal_mem hD hP hx
  obtain ⟨hall, -⟩ := hD
  obtain ⟨⟨hne, hch, hcl⟩, hnd⟩ := hall P hP
  exact ⟨hne, hch, hcl, hnd, fun d hd had => halpha d (hPc d hd) (hPc _ had)⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.infraPetal_isSimple

/-- **A minimal petal**: a petal of minimal length; it is a simple closed walk `B ⊆ c`. -/
theorem infraPetal_exists_min_petal {M : CombMap.{v}} {c : List M.Dart}
    (hc : IsClosedDartWalk M c) (halpha : ∀ d ∈ c, M.alpha d ∉ c) :
    ∃ (Ps : List (List M.Dart)) (B : List M.Dart), infraPetal_IsDecomp M c Ps ∧ B ∈ Ps ∧
      IsSimpleClosedWalk M B ∧ (∀ P ∈ Ps, B.length ≤ P.length) ∧ ∀ x ∈ B, x ∈ c := by
  obtain ⟨Ps, hne, hD⟩ := infraPetal_exists_decomp hc
  obtain ⟨B, hB, hmin⟩ := infraPetal_exists_min Ps hne
  exact ⟨Ps, B, hD, hB, infraPetal_isSimple hD halpha hB, hmin,
    fun x hx => infraPetal_mem hD hB hx⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.infraPetal_exists_min_petal

/-- The minimal petal of a closed boundary cycle. -/
theorem infraPetal_boundary_min_petal {M : CombMap.{v}} {F : Finset M.Face}
    (c : BoundaryCycle M F) (hc : IsClosedDartWalk M c.cycle) :
    ∃ (Ps : List (List M.Dart)) (B : List M.Dart), infraPetal_IsDecomp M c.cycle Ps ∧
      B ∈ Ps ∧ IsSimpleClosedWalk M B ∧ (∀ P ∈ Ps, B.length ≤ P.length) ∧
      ∀ x ∈ B, x ∈ c.cycle :=
  infraPetal_exists_min_petal hc fun _ hd => p10QM_alpha_not_mem M c hd

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.infraPetal_boundary_min_petal

/-- On a closed walk, the vertices of `B` are the start vertices of its darts. -/
theorem infraPetal_onB_iff {M : CombMap.{v}} {B : List M.Dart} (hB : IsClosedDartWalk M B)
    (w : M.Vertex) : p10QS_OnB M B w ↔ ∃ x ∈ B, M.vertexOf x = w := by
  constructor
  · rintro ⟨x, hx, h | h⟩
    · exact ⟨x, hx, h⟩
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      by_cases hi1 : i + 1 < B.length
      · exact ⟨B[i + 1], List.getElem_mem hi1,
          (IsClosedDartWalk.vertexOf_alpha_getElem hB hi1).symm.trans h⟩
      · obtain rfl : i = B.length - 1 := by omega
        have h0 : 0 < B.length := by omega
        exact ⟨B[0], List.getElem_mem h0,
          (IsClosedDartWalk.vertexOf_alpha_getElem_last hB h0).symm.trans h⟩
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, Or.inl h⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.infraPetal_onB_iff

/-- **The rest of `c` meets `B` only at vertices.**  For a closed walk `B ⊆ c` with no reverse
pairs in `c`, a dart `d ∈ c` off `B` is not retained by `B`; if it starts on `B`, it starts
where a different dart of `c` on `B` starts; if it ends on `B`, it ends at the start of a dart
of `B`. -/
theorem infraPetal_rest_meets {M : CombMap.{v}} {c B : List M.Dart}
    (hB : IsClosedDartWalk M B) (hBc : ∀ x ∈ B, x ∈ c) (halpha : ∀ d ∈ c, M.alpha d ∉ c)
    {d : M.Dart} (hd : d ∈ c) (hdB : d ∉ B) :
    ¬walkKeep M B d ∧
      (p10QS_OnB M B (M.vertexOf d) →
        ∃ x ∈ B, x ∈ c ∧ x ≠ d ∧ M.vertexOf x = M.vertexOf d) ∧
      (p10QS_OnB M B (M.vertexOf (M.alpha d)) →
        ∃ x ∈ B, M.vertexOf x = M.vertexOf (M.alpha d)) := by
  refine ⟨?_, fun h => ?_, fun h => (infraPetal_onB_iff hB _).mp h⟩
  · rintro (h | h)
    · exact hdB h
    · exact halpha d hd (hBc _ h)
  · obtain ⟨x, hx, hxd⟩ := (infraPetal_onB_iff hB _).mp h
    refine ⟨x, hx, hBc x hx, fun h' => hdB ?_, hxd⟩
    rw [← h']
    exact hx

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.infraPetal_rest_meets

end Shared

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove
