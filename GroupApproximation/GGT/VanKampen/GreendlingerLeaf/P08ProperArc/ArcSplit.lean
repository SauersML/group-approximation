import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkSides
import GroupApproximation.GGT.VanKampen.ClosedWalkPinchSplit
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPieces
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellPocketWalk
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketSectionFaceSet
import GroupApproximation.Meta.AxiomGuard

/-!
# A proper source arc for the section pocket: list and arc bookkeeping

This directory proves `OsinSectionPocketFaceSetProperSectionStatement`: for two distinct exterior
regions `x`, `y` of the same relator cell `i` targeting the same section, there is an O-equivalent
lettered copy carrying a pocket face set whose boundary is a closed walk and whose source arc is a
*proper* arc of the source cell.

## Mathematical proof

Pass to the copy-clean O-equivalent copy `S₄` (`PocketFaceSetOnCopy.exists_copyClean`, with the
proved `RegionPairThickening.sectionPocketRegionsCopy`), transport the pair `(a, b)` to an exterior
pair `(a', b')` of a cell `i'` of `S₄`, and order the pair so that `x` starts not later than `y` on
the exterior boundary (`le_total`).

1. **The pocket walk.** `PocketWalk.exists_of_le` gives the walk
   `w = y.leftSide ++ (xA ++ Gap ++ yA)⁻¹ ++ x.rightSide ++ T`, where `xA`, `yA` are the source arcs
   of `x`, `y`, `Gap` an arc of `i'` between them, and `T` the target arc, from the start of `x`'s
   target arc to the end of `y`'s.  Copy-cleanliness makes `w` a noncrossing closed walk
   (`PocketWalk.noncrossing_of_copyClean`), so its side `F = sideFaces w` has boundary cycle
   exactly `w` and avoids the exterior face; `sectionPocketKeptCell` gives a relator cell in `F`.
2. **Splitting the arcs.** The source arc `xA ++ Gap ++ yA` has the prefix arc `T' = xA ++ Gap`,
   with `|T'| + |yA| = |source arc|`.  The target arc `T` has the prefix arc `t₂` ending where
   `y`'s target arc `yT` starts, with `T = t₂ ++ yT` (both inside the exterior cycle, since the
   pocket ends at most at a section cut).  Hence `w = yL ++ yA⁻¹ ++ T'⁻¹ ++ xR ++ t₂ ++ yT`, and
   the boundary cycle of region `y` is `yA⁻¹ ++ yR ++ yT ++ yL`.
3. **Every face of `y` is on the side of `w`.** Boundary steps of `y` move between darts by internal
   moves of `y`; an internal dart `t` of `y` (both faces in `y`) is not on `w` nor reversed on `w`
   (`PocketWalk.internal_not_walkKeep`), so its two faces are on the same side of `w`.  A dart of
   `yT` lies on `w`, so its face is in `F`; chaining along the boundary cycle of `y`, every boundary
   dart of `y` has its face in `F`.
4. **The right side of `y` is off the walk.** A dart `e` of `yR` is not on `w` and `α e` is not on
   `w`: on `yL` it contradicts nodup of `y`'s cycle, resp. `yL` leaving `y` while `α e` enters it;
   on the source arc it contradicts copy-cleanliness `side_cell`, resp. cells avoiding regions; on
   `xR` it contradicts disjointness, resp. `CopyClean.regions`; on `T` it contradicts `side_outer`,
   resp. regions avoiding the exterior face.
5. **Removing `y`.** Put `F' = F \ y`.  A dart `d` is a boundary dart of `F'` iff
   `d ∈ yR⁻¹ ++ T'⁻¹ ++ xR ++ t₂`.  (→) If `faceOf (α d) ∈ F`, then `faceOf (α d) ∈ y`, so `α d` is on
   `y`'s cycle but `faceOf d ∉ y`; `α d` on `yA⁻¹, yT, yL ⊆ w` would put `faceOf d` outside `F`, so
   `α d ∈ yR` and `d ∈ yR⁻¹`.  Otherwise `d` is a boundary dart of `F`, i.e. `d ∈ w`; `d` on
   `yL, yA⁻¹, yT` would put `faceOf d ∈ y`, so `d ∈ T'⁻¹ ++ xR ++ t₂`.  (←) For `d ∈ yR⁻¹`: `α d ∈ yR`
   has face in `y ⊆ F` (step 3) and `faceOf d ∉ y`; step 4 moves `faceOf d` into `F`.  For
   `d ∈ T'⁻¹ ++ xR ++ t₂ ⊆ w`: `faceOf d ∈ F`, `faceOf (α d) ∉ F`; were `faceOf d ∈ y`, either
   `faceOf (α d) ∈ y` (an internal dart on `w`, impossible) or `d` is on `y`'s cycle, contradicting
   nodup of `w` or step 4.
6. **The new pocket.** The cycle `yR⁻¹ ++ T'⁻¹ ++ xR ++ t₂` is nodup (from the nodup of the two
   cycles and step 4), a closed walk (split the walks `w` and `y`'s cycle at the shared vertices,
   reverse `yR`, and glue), with sides `yR⁻¹` and `xR` of bounded length and norm.  The source cell
   is not in `F'` (the source arc is on `w`, reversed), the exterior face is not in `F` (hence not
   in `F'`), and the kept cell of `F` is not in `y` (cells avoid regions), so it is in `F'`.  The
   target arc `t₂` starts at `x`'s target start and ends at `y`'s target start, inside the section.
7. **Properness.** `|T'| = |source arc| - |yA| ≤ |cell i'| - |yA| < |cell i'|`, since the section
   family is nondegenerate: `0 < |yA|`.

This module holds the list, arc and walk bookkeeping.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P08ProperArc

universe u w v

open Embedded SameCellPocketWalk

/-- **Along a chain of an equivalence-preserving relation, a predicate is constant.** -/
theorem iff_of_isChain {α : Type*} {R : α → α → Prop} {Q : α → Prop}
    (hR : ∀ a b, R a b → (Q a ↔ Q b)) {l : List α} (h : l.IsChain R) :
    ∀ a ∈ l, ∀ b ∈ l, (Q a ↔ Q b) := by
  induction h with
  | nil => intro _ ha; simp at ha
  | singleton c =>
    intro a ha b hb
    obtain rfl := List.mem_singleton.mp ha
    obtain rfl := List.mem_singleton.mp hb
    exact Iff.rfl
  | @cons_cons c d t hr _ ih =>
    have hc : ∀ e ∈ c :: d :: t, (Q e ↔ Q d) := by
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact hR _ _ hr
      · exact ih e he d List.mem_cons_self
    intro a ha b hb
    exact (hc a ha).trans (hc b hb).symm

/-- An arc that does not wrap around is a plain sublist. -/
theorem darts_eq_drop_take {Dart : Type v} {cycle : List Dart} (A : CyclicArc cycle)
    (h : A.start.1 + A.length ≤ cycle.length) :
    A.darts = (cycle.drop A.start.1).take A.length := by
  have hlen : A.length ≤ (cycle.drop A.start.1).length := by
    rw [List.length_drop]; omega
  show (cycle.drop A.start.1 ++ cycle.take A.start.1).take A.length = _
  exact List.take_append_of_le_length hlen

/-- **A prefix of an arc is an arc.** -/
theorem exists_prefix {Dart : Type v} {cycle : List Dart} (A : CyclicArc cycle)
    {P S : List Dart} (h : A.darts = P ++ S) :
    ∃ B : CyclicArc cycle, B.start = A.start ∧ B.length + S.length = A.length ∧ B.darts = P := by
  have hl : P.length + S.length = A.length := by
    rw [← A.darts_length, h, List.length_append]
  have hle : P.length ≤ cycle.length := by have := A.length_le; omega
  refine ⟨⟨A.start, P.length, hle⟩, rfl, hl, ?_⟩
  show A.rotated.take P.length = P
  have hP : P.length ≤ A.length := by omega
  calc A.rotated.take P.length = (A.rotated.take A.length).take P.length := by
        rw [List.take_take, Nat.min_eq_left hP]
    _ = P := by
        show A.darts.take P.length = P
        rw [h]
        exact List.take_left' rfl

/-- **Cutting a common suffix arc off a non-wrapping arc** leaves an arc ending where the suffix
starts. -/
theorem exists_prefix_of_suffix {Dart : Type v} {cycle : List Dart} (A Y : CyclicArc cycle)
    (hAY : A.start.1 ≤ Y.start.1) (hend : A.start.1 + A.length = Y.start.1 + Y.length)
    (hn : A.start.1 + A.length ≤ cycle.length) :
    ∃ B : CyclicArc cycle, B.start = A.start ∧ B.start.1 + B.length = Y.start.1 ∧
      A.darts = B.darts ++ Y.darts := by
  have hBle : Y.start.1 - A.start.1 ≤ cycle.length := by omega
  refine ⟨⟨A.start, Y.start.1 - A.start.1, hBle⟩, rfl, ?_, ?_⟩
  · show A.start.1 + (Y.start.1 - A.start.1) = Y.start.1
    omega
  · have hB : (⟨A.start, Y.start.1 - A.start.1, hBle⟩ : CyclicArc cycle).darts =
        (cycle.drop A.start.1).take (Y.start.1 - A.start.1) :=
      darts_eq_drop_take _ (by show A.start.1 + (Y.start.1 - A.start.1) ≤ cycle.length; omega)
    rw [hB, darts_eq_drop_take A hn, darts_eq_drop_take Y (by omega)]
    have hlen : A.length = (Y.start.1 - A.start.1) + Y.length := by omega
    rw [hlen, List.take_add, List.drop_drop, Nat.add_sub_cancel' hAY]

/-- In a nodup four-part list, a member of the third part is in no other part. -/
theorem not_mem_of_nodup_mid {α : Type*} {l₁ l₂ l₃ l₄ : List α} {a : α}
    (h : (l₁ ++ l₂ ++ l₃ ++ l₄).Nodup) (ha : a ∈ l₃) : a ∉ l₁ ∧ a ∉ l₂ ∧ a ∉ l₄ := by
  obtain ⟨h123, -, h1234⟩ := List.nodup_append.mp h
  obtain ⟨-, -, h123'⟩ := List.nodup_append.mp h123
  exact ⟨fun h1 => h123' a (List.mem_append_left _ h1) a ha rfl,
    fun h2 => h123' a (List.mem_append_right _ h2) a ha rfl,
    fun h4 => h1234 a (List.mem_append_right _ ha) a h4 rfl⟩

/-- In a nodup four-part list, a member of the second part is in no other part. -/
theorem not_mem_of_nodup_snd {α : Type*} {l₁ l₂ l₃ l₄ : List α} {a : α}
    (h : (l₁ ++ l₂ ++ l₃ ++ l₄).Nodup) (ha : a ∈ l₂) : a ∉ l₁ ∧ a ∉ l₃ ∧ a ∉ l₄ := by
  obtain ⟨h123, -, h1234⟩ := List.nodup_append.mp h
  obtain ⟨h12, -, h123'⟩ := List.nodup_append.mp h123
  obtain ⟨-, -, h12'⟩ := List.nodup_append.mp h12
  exact ⟨fun h1 => h12' a h1 a ha rfl,
    fun h3 => h123' a (List.mem_append_right _ ha) a h3 rfl,
    fun h4 => h1234 a (List.mem_append_left _ (List.mem_append_right _ ha)) a h4 rfl⟩

/-- In a nodup four-part list, a member of the first part is in no other part. -/
theorem not_mem_of_nodup_fst {α : Type*} {l₁ l₂ l₃ l₄ : List α} {a : α}
    (h : (l₁ ++ l₂ ++ l₃ ++ l₄).Nodup) (ha : a ∈ l₁) : a ∉ l₂ ∧ a ∉ l₃ ∧ a ∉ l₄ := by
  obtain ⟨h123, -, h1234⟩ := List.nodup_append.mp h
  obtain ⟨h12, -, h123'⟩ := List.nodup_append.mp h123
  obtain ⟨-, -, h12'⟩ := List.nodup_append.mp h12
  exact ⟨fun h2 => h12' a ha a h2 rfl,
    fun h3 => h123' a (List.mem_append_left _ ha) a h3 rfl,
    fun h4 => h1234 a (List.mem_append_left _ (List.mem_append_left _ ha)) a h4 rfl⟩

/-- A noncrossing closed walk is a walk from its first vertex to itself. -/
theorem isWalkFromTo_of_noncrossing {M : CombMap.{v}} {w : List M.Dart}
    (hw : IsNoncrossingClosedWalk M w) :
    IsWalkFromTo M w (M.vertexOf (w.head hw.ne_nil)) (M.vertexOf (w.head hw.ne_nil)) := by
  refine isWalkFromTo_of_isChain_closes hw.ne_nil hw.chain ?_
  intro a ha b hb
  obtain rfl := Option.some.inj
    ((List.getLast?_eq_some_getLast hw.ne_nil).symm.trans (Option.mem_def.mp ha))
  obtain rfl := Option.some.inj
    ((List.head?_eq_some_head hw.ne_nil).symm.trans (Option.mem_def.mp hb))
  exact hw.closes

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {X : DiscDiagram.{u, w, v} W}

/-- For the exterior target, the boundary darts of the target arc are the arc itself. -/
theorem targetBoundaryDarts_none (X : DiscDiagram.{u, w, v} W) {target : Option (Fin X.rCellCount)}
    (ht : target = none) (arc : CyclicArc (targetDarts X target)) :
    targetBoundaryDarts X target arc = arc.darts := by
  subst ht; rfl

/-- A pocket face set whose boundary cycle is a closed dart walk is in walk order. -/
theorem closedWalk_of_isClosedDartWalk {D : RelGenSet G Lambda} {eps lo hi : ℕ}
    {K : PocketFaceSet D eps X lo hi} (h : IsClosedDartWalk X.toCombMap K.boundary.cycle) :
    K.ClosedWalk := by
  obtain ⟨_, hch, hcl⟩ := h
  exact ⟨hch, hcl⟩

/-- A dart whose reverse lies in `l` lies in `invDarts X l`. -/
theorem mem_invDarts_of_alpha_mem {l : List X.toCombMap.Dart} {d : X.toCombMap.Dart}
    (h : X.toCombMap.alpha d ∈ l) : d ∈ invDarts X l := by
  have hm := List.mem_map_of_mem (f := X.toCombMap.alpha) (List.mem_reverse.mpr h)
  rw [X.toCombMap.alpha_involutive d] at hm
  exact hm

/-- The reverse of a dart of `invDarts X l` lies in `l`. -/
theorem alpha_mem_of_mem_invDarts {l : List X.toCombMap.Dart} {d : X.toCombMap.Dart}
    (h : d ∈ invDarts X l) : X.toCombMap.alpha d ∈ l := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
  rw [X.toCombMap.alpha_involutive e]
  exact List.mem_reverse.mp he

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P08ProperArc
