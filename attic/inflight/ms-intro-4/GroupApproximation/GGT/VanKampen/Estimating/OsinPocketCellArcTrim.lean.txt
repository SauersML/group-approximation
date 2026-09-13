import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellPinchStep
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketArcTrim
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketFullArc
import GroupApproximation.Meta.AxiomGuard

/-!
# Trims and full arcs of the pocket between two cells

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2` between two regions joining the cells `Π_i` and `Π_j`.

The cell analogues of `Estimating/OsinPocketArcTrim.lean` and `Estimating/OsinPocketFullArc.lean`
(lane w1-binder-7), reusing their arc-level layer: `CyclicArc.dropLastArc`,
`PocketFaceSet.invDarts_eq_getLast_cons`, `PocketFaceSet.invDarts_eq_tail_append` and the
`PocketFullArc` helpers.

Both arcs of a cell pocket are read backwards, so the first dart of each reversed arc is the
reversal of the last dart of the arc, and it follows the side before it.

* `CellPocketFaceSet.trimFirstLast`: that dart of the first arc joins the first side, when the side
  is shorter than `ε` and the arc has at least two darts.
* `CellPocketFaceSet.trimSecondLast`: the same for the second arc and the second side.
* Both trims keep the boundary cycle, so they keep walk order, repeated visits and simplicity, and
  they shorten the arc.
* `CellPocketFaceSet.not_simple_of_full_firstArc`, `not_simple_of_full_secondArc`: a cell pocket
  whose arc is all of its cell is not simple.  Unlike the section case, the rest of the walk is
  never empty, since the other arc is nonempty.

So a pinched cell pocket with a full arc must change its arcs or sides before it can become
simple, which is where the pinch step needs room on a side.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121 at origin/main 68481e4d7,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7(b);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded PocketFullArc

namespace CellPocketFaceSet

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- The first arc of a cell pocket has a dart. -/
theorem firstArc_darts_ne_nil (K : CellPocketFaceSet D eps X i j) : K.firstArc.darts ≠ [] :=
  List.ne_nil_of_length_pos (by rw [CyclicArc.darts_length]; exact K.firstArc_pos)

/-- The second arc of a cell pocket has a dart. -/
theorem secondArc_darts_ne_nil (K : CellPocketFaceSet D eps X i j) : K.secondArc.darts ≠ [] :=
  List.ne_nil_of_length_pos (by rw [CyclicArc.darts_length]; exact K.secondArc_pos)

/-- **Trim the first arc into the first side.**  The first dart of the reversed first arc, the
reversal of the last dart of the arc, joins the first side, when the first side is shorter than `ε`
and the arc has at least two darts. -/
noncomputable def trimFirstLast (K : CellPocketFaceSet D eps X i j)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (hroom : K.firstSide.length < eps) (hlong : 1 < K.firstArc.length) :
    CellPocketFaceSet D eps X i j where
  faces := K.faces
  outerFace_not_mem := K.outerFace_not_mem
  first_not_mem := K.first_not_mem
  second_not_mem := K.second_not_mem
  kept := K.kept
  kept_mem := K.kept_mem
  firstArc := K.firstArc.dropLastArc
  secondArc := K.secondArc
  firstSide := K.firstSide ++ [X.toCombMap.alpha (K.firstArc.darts.getLast K.firstArc_darts_ne_nil)]
  secondSide := K.secondSide
  boundary := K.boundary
  decomposition := by
    rw [K.decomposition, CyclicArc.dropLastArc_darts,
      PocketFaceSet.invDarts_eq_getLast_cons K.firstArc_darts_ne_nil]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  firstArc_pos := by
    show 0 < K.firstArc.length - 1
    omega
  secondArc_pos := K.secondArc_pos
  firstSide_length_le := by
    rw [List.length_append, List.length_singleton]
    omega
  secondSide_length_le := K.secondSide_length_le
  firstSide_norm_le := (PocketFaceSet.wordNorm_dartWord_le_length hlabel _).trans (by
    rw [List.length_append, List.length_singleton]
    omega)
  secondSide_norm_le := K.secondSide_norm_le

/-- **Trim the second arc into the second side.**  The first dart of the reversed second arc, the
reversal of the last dart of the arc, joins the second side, when the second side is shorter than
`ε` and the arc has at least two darts. -/
noncomputable def trimSecondLast (K : CellPocketFaceSet D eps X i j)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (hroom : K.secondSide.length < eps) (hlong : 1 < K.secondArc.length) :
    CellPocketFaceSet D eps X i j where
  faces := K.faces
  outerFace_not_mem := K.outerFace_not_mem
  first_not_mem := K.first_not_mem
  second_not_mem := K.second_not_mem
  kept := K.kept
  kept_mem := K.kept_mem
  firstArc := K.firstArc
  secondArc := K.secondArc.dropLastArc
  firstSide := K.firstSide
  secondSide :=
    K.secondSide ++ [X.toCombMap.alpha (K.secondArc.darts.getLast K.secondArc_darts_ne_nil)]
  boundary := K.boundary
  decomposition := by
    rw [K.decomposition, CyclicArc.dropLastArc_darts,
      PocketFaceSet.invDarts_eq_getLast_cons K.secondArc_darts_ne_nil]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  firstArc_pos := K.firstArc_pos
  secondArc_pos := by
    show 0 < K.secondArc.length - 1
    omega
  firstSide_length_le := K.firstSide_length_le
  secondSide_length_le := by
    rw [List.length_append, List.length_singleton]
    omega
  firstSide_norm_le := K.firstSide_norm_le
  secondSide_norm_le := (PocketFaceSet.wordNorm_dartWord_le_length hlabel _).trans (by
    rw [List.length_append, List.length_singleton]
    omega)

section Trim

variable (K : CellPocketFaceSet D eps X i j)
  (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))

theorem closedWalk_trimFirstLast (hroom : K.firstSide.length < eps)
    (hlong : 1 < K.firstArc.length) (hK : K.ClosedWalk) :
    (K.trimFirstLast hlabel hroom hlong).ClosedWalk :=
  hK

theorem repeatedVisits_trimFirstLast (hroom : K.firstSide.length < eps)
    (hlong : 1 < K.firstArc.length) :
    (K.trimFirstLast hlabel hroom hlong).repeatedVisits = K.repeatedVisits :=
  rfl

theorem simple_trimFirstLast_iff (hroom : K.firstSide.length < eps)
    (hlong : 1 < K.firstArc.length) : (K.trimFirstLast hlabel hroom hlong).Simple ↔ K.Simple :=
  Iff.rfl

/-- The trimmed first arc is shorter than the first arc. -/
theorem trimFirstLast_firstArc_lt (hroom : K.firstSide.length < eps)
    (hlong : 1 < K.firstArc.length) :
    (K.trimFirstLast hlabel hroom hlong).firstArc.length < K.firstArc.length := by
  show K.firstArc.length - 1 < K.firstArc.length
  omega

theorem closedWalk_trimSecondLast (hroom : K.secondSide.length < eps)
    (hlong : 1 < K.secondArc.length) (hK : K.ClosedWalk) :
    (K.trimSecondLast hlabel hroom hlong).ClosedWalk :=
  hK

theorem repeatedVisits_trimSecondLast (hroom : K.secondSide.length < eps)
    (hlong : 1 < K.secondArc.length) :
    (K.trimSecondLast hlabel hroom hlong).repeatedVisits = K.repeatedVisits :=
  rfl

theorem simple_trimSecondLast_iff (hroom : K.secondSide.length < eps)
    (hlong : 1 < K.secondArc.length) : (K.trimSecondLast hlabel hroom hlong).Simple ↔ K.Simple :=
  Iff.rfl

/-- The trimmed second arc is shorter than the second arc. -/
theorem trimSecondLast_secondArc_lt (hroom : K.secondSide.length < eps)
    (hlong : 1 < K.secondArc.length) :
    (K.trimSecondLast hlabel hroom hlong).secondArc.length < K.secondArc.length := by
  show K.secondArc.length - 1 < K.secondArc.length
  omega

end Trim

/-- On a full first arc the face rotation takes the last dart to the first. -/
theorem facePerm_firstArc_of_full (K : CellPocketFaceSet D eps X i j)
    (hfull : K.firstArc.length = (cellDarts X i).length) :
    ∀ x ∈ K.firstArc.darts.getLast?, ∀ y ∈ K.firstArc.darts.head?,
      X.toCombMap.facePerm x = y := by
  rw [darts_eq_rotate_of_full K.firstArc hfull]
  exact cyclicRel_rotate (X.faceBoundary (cell X i).face).chain
    (faceBoundary_cyclic (X.faceBoundary (cell X i).face))
    (Nat.le_of_lt_succ K.firstArc.start.isLt)

/-- On a full second arc the face rotation takes the last dart to the first. -/
theorem facePerm_secondArc_of_full (K : CellPocketFaceSet D eps X i j)
    (hfull : K.secondArc.length = (cellDarts X j).length) :
    ∀ x ∈ K.secondArc.darts.getLast?, ∀ y ∈ K.secondArc.darts.head?,
      X.toCombMap.facePerm x = y := by
  rw [darts_eq_rotate_of_full K.secondArc hfull]
  exact cyclicRel_rotate (X.faceBoundary (cell X j).face).chain
    (faceBoundary_cyclic (X.faceBoundary (cell X j).face))
    (Nat.le_of_lt_succ K.secondArc.start.isLt)

/-- **A cell pocket with a full first arc is not simple.**  The first dart of the reversed first
arc and the dart after its last dart start at the vertex of the first dart of the arc, and the
second arc makes the rest of the walk nonempty. -/
theorem not_simple_of_full_firstArc (K : CellPocketFaceSet D eps X i j)
    (hfull : K.firstArc.length = (cellDarts X i).length) : ¬ K.Simple := by
  intro hK
  have hS : IsSimpleClosedWalk X.toCombMap K.boundary.cycle := hK
  have hne := K.firstArc_darts_ne_nil
  have hlastfirst : X.toCombMap.facePerm (K.firstArc.darts.getLast hne) =
      K.firstArc.darts.head hne :=
    facePerm_firstArc_of_full K hfull _
      (by rw [List.getLast?_eq_some_getLast hne]; exact Option.mem_some_iff.mpr rfl)
      _ (by rw [List.head?_eq_some_head hne]; exact Option.mem_some_iff.mpr rfl)
  have hv1 : X.toCombMap.vertexOf (X.toCombMap.alpha (K.firstArc.darts.getLast hne)) =
      X.toCombMap.vertexOf (K.firstArc.darts.head hne) := by
    rw [vertexOf_alpha_eq_facePerm, hlastfirst]
  have hv2 : X.toCombMap.vertexOf (X.toCombMap.alpha (X.toCombMap.alpha
      (K.firstArc.darts.head hne))) = X.toCombMap.vertexOf (K.firstArc.darts.head hne) := by
    rw [X.toCombMap.alpha_involutive]
  have hmem : X.toCombMap.alpha (K.firstArc.darts.getLast hne) ∈ invDarts X K.firstArc.darts :=
    List.mem_map_of_mem (List.mem_reverse.mpr (List.getLast_mem hne))
  have E2 := PocketFaceSet.invDarts_eq_tail_append (X := X) hne
  have hnd := hS.vertex_nodup
  have h2 : K.secondSide ++ invDarts X K.secondArc.darts ≠ [] := fun h =>
    K.secondArc_darts_ne_nil
      (List.reverse_eq_nil_iff.mp (List.map_eq_nil_iff.mp (List.append_eq_nil_iff.mp h).2))
  obtain ⟨b, rest, hb⟩ := List.exists_cons_of_ne_nil h2
  have hc : K.boundary.cycle = (K.firstSide ++ invDarts X K.firstArc.darts) ++ (b :: rest) := by
    rw [K.decomposition,
      List.append_assoc (K.firstSide ++ invDarts X K.firstArc.darts) K.secondSide
        (invDarts X K.secondArc.darts), hb]
  have hc2 : K.boundary.cycle = (K.firstSide ++ K.firstArc.darts.tail.reverse.map
      X.toCombMap.alpha) ++ X.toCombMap.alpha (K.firstArc.darts.head hne) :: b :: rest := by
    rw [hc, E2]
    simp only [List.append_assoc, List.singleton_append]
  have hch := hS.chain
  rw [hc2] at hch
  obtain ⟨-, hxb, -⟩ := List.isChain_append_cons_cons.mp hch
  rw [hc, List.map_append, List.nodup_append] at hnd
  exact hnd.2.2 _ (List.mem_map_of_mem (List.mem_append_right _ hmem)) _
    (List.mem_map_of_mem (by simp)) (hv1.trans (hv2.symm.trans hxb))

/-- **A cell pocket with a full second arc is not simple.**  The vertex after the last dart of the
walk is the vertex of the first dart of the second arc, which is where the reversed second arc
starts, and the walk closes at the vertex of its own first dart. -/
theorem not_simple_of_full_secondArc (K : CellPocketFaceSet D eps X i j)
    (hfull : K.secondArc.length = (cellDarts X j).length) : ¬ K.Simple := by
  intro hK
  have hS : IsSimpleClosedWalk X.toCombMap K.boundary.cycle := hK
  have hne := K.secondArc_darts_ne_nil
  have hlastfirst : X.toCombMap.facePerm (K.secondArc.darts.getLast hne) =
      K.secondArc.darts.head hne :=
    facePerm_secondArc_of_full K hfull _
      (by rw [List.getLast?_eq_some_getLast hne]; exact Option.mem_some_iff.mpr rfl)
      _ (by rw [List.head?_eq_some_head hne]; exact Option.mem_some_iff.mpr rfl)
  have hv1 : X.toCombMap.vertexOf (X.toCombMap.alpha (K.secondArc.darts.getLast hne)) =
      X.toCombMap.vertexOf (K.secondArc.darts.head hne) := by
    rw [vertexOf_alpha_eq_facePerm, hlastfirst]
  have hv2 : X.toCombMap.vertexOf (X.toCombMap.alpha (X.toCombMap.alpha
      (K.secondArc.darts.head hne))) = X.toCombMap.vertexOf (K.secondArc.darts.head hne) := by
    rw [X.toCombMap.alpha_involutive]
  have hmem : X.toCombMap.alpha (K.secondArc.darts.getLast hne) ∈ invDarts X K.secondArc.darts :=
    List.mem_map_of_mem (List.mem_reverse.mpr (List.getLast_mem hne))
  have E2 := PocketFaceSet.invDarts_eq_tail_append (X := X) hne
  have hnd := hS.vertex_nodup
  have h1 : K.firstSide ++ invDarts X K.firstArc.darts ++ K.secondSide ≠ [] := fun h =>
    K.firstArc_darts_ne_nil (List.reverse_eq_nil_iff.mp (List.map_eq_nil_iff.mp
      (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp h).1).2))
  obtain ⟨b, rest, hb⟩ := List.exists_cons_of_ne_nil h1
  have hc : K.boundary.cycle = (b :: rest) ++ invDarts X K.secondArc.darts := by
    rw [K.decomposition, hb]
  have hc' : K.boundary.cycle = ((b :: rest) ++ K.secondArc.darts.tail.reverse.map
      X.toCombMap.alpha) ++ [X.toCombMap.alpha (K.secondArc.darts.head hne)] := by
    rw [hc, E2, List.append_assoc]
  have hcl := closes_mem hS
  rw [hc'] at hcl
  have hvb := hcl (X.toCombMap.alpha (K.secondArc.darts.head hne))
    (mem_getLast?_append_singleton _ _) b (Option.mem_some_iff.mpr rfl)
  rw [hc, List.map_append, List.nodup_append] at hnd
  exact hnd.2.2 _ (List.mem_map_of_mem (by simp)) _ (List.mem_map_of_mem hmem)
    (hvb.symm.trans (hv2.trans hv1.symm))

end CellPocketFaceSet

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.trimFirstLast
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.trimSecondLast
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.repeatedVisits_trimFirstLast
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.trimSecondLast_secondArc_lt
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.not_simple_of_full_firstArc
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.not_simple_of_full_secondArc
